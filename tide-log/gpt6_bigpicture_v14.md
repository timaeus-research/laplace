## Bottom line

The general-\(d\) milestone is **not just box packaging**. What you already have is a general-multiplicity result for the **particular quadratic primitive underlying `iterChart`**. The equal-ratio monomial theorem still needs:

1. weighted power substitution;
2. universal product density;
3. a genuine `Fin d → ℝ` box bridge;
4. a **general-\(\lambda\)** Gamma/log-moment asymptotic.

The existing iterated primitives are a useful special-case regression test, but they do not, from the declarations shown, supply item 4 for arbitrary \(\lambda>0\).

Separately, I would put **unequal-leading-term quotient asymptotics** ahead of completing the whole general-\(d\) programme. That is highly paper-facing and should reuse substantially more of the current machinery. But the inference “vanishes at the corner, therefore the power of \(N\) improves” needs correction.

---

## (a) What is done, and the minimal new chain?

### What the current files actually buy

| Existing material | Relevance to this milestone |
|---|---|
| `IteratedLogPrimitive` | Repeated logarithmic integration of the existing quadratic kernel; growth, continuity, and substitution infrastructure |
| `LogPowerGeneralD` | Arbitrary logarithmic multiplicity for the recursively defined **specific** chart |
| `TaylorProjections` | Algebraic organisation of faces/remainders; not needed for the pure monomial density theorem |
| `LogSquaredThreeD` | Supporting analytic bounds already subsumed or generalised by the iterated-primitive layer |

In particular, proving an asymptotic for a recursive `iterChart` does **not by itself** prove that it equals a \(d\)-dimensional Lebesgue integral. Your proposed separate bridge is the right boundary.

### First define recursive integration, without `Fin d`

I would use an ENNReal-valued test function and ordinary restricted volume at each recursive step:

```lean
-- Schematic Lean: not a checked declaration.
noncomputable def productIntegral (λ : ℝ) :
    ℕ → (ℝ → ℝ≥0∞) → ℝ≥0∞
  | 0, g => g 1
  | n + 1, g =>
      ∫⁻ t in Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (t ^ (λ - 1)) *
          productIntegral λ n (fun z => g (t * z))
```

Advantages:

- dimension zero has the correct empty-product interpretation;
- the successor equation is definitional;
- no dependent coordinate manipulations occur in the density proof;
- integrating against restricted volume avoids initially having to establish typeclass infrastructure for a weighted measure;
- arbitrary nonnegative measurable \(g\), including functions with infinite integral, is supported.

The principal theorem should be indexed by `m + 1`:

\[
R_{\lambda,m+1}(g)
=
\frac1{m!}
\int_{(0,1]}
g(z)\,z^{\lambda-1}(-\log z)^m\,dz.
\]

In Lean, the powers and weight go into `ENNReal.ofReal`, and the factorial coefficient is an ENNReal constant. Use `Measurable g`, and initially assume \(0<\lambda\). The latter is stronger than needed for the density identity alone, but it matches the milestone and simplifies subsequent finiteness results.

### The induction really has three analytic ingredients

For the step from dimension \(d\) to \(d+1\), after applying the induction hypothesis, one has

\[
\frac1{(d-1)!}\int_0^1\int_0^1
g(tz)t^{\lambda-1}z^{\lambda-1}(-\log z)^{d-1}\,dz\,dt.
\]

For fixed \(t>0\), put \(w=tz\):

\[
=\frac1{(d-1)!}\int_0^1\int_0^t
g(w)w^{\lambda-1}
\frac{(-\log(w/t))^{d-1}}{t}\,dw\,dt.
\]

Tonelli changes the triangular region into \(0<w\le1,\ w\le t\le1\). Your core identity then finishes the step.

Thus the minimal helpers are:

1. positive scaling substitution for a nonnegative integral;
2. Tonelli on the triangular region;
3. the logarithmic FTC identity.

Do not underestimate items 1–2 merely because the paper compresses them to one line.

### Keep the box theorem separate

Prove a generic bridge first:

\[
R_{\lambda,d}(g)
=
\int_{(0,1]^d}
g\!\left(\prod_i t_i\right)
\prod_i t_i^{\lambda-1}\,dt.
\]

Then prove a coordinatewise power-substitution bridge for the original monomial integral. This avoids coupling the density induction to heterogeneous \(k_i,h_i\).

Use the function space `Fin d → ℝ`, not a subtype of box-valued functions. A set integral, or a full-space integral of an indicator, is easier to transport under coordinate splitting. No `//` is necessary.

### The Mathlib splitting route

The theorem you found,

```lean
MeasureTheory.volume_preserving_piFinSuccAbove
```

is precisely the kind of bridge needed. It supplies the measure-preserving coordinate-splitting equivalence. Combine it with:

- the relevant measure-preserving integral-composition theorem;
- `MeasureTheory.lintegral_prod` for ENNReal;
- `MeasureTheory.integral_prod` for Bochner, with integrability established.

Check the actual orientation before choosing `.symm`; I would not infer it from the declaration name alone.

Useful checks/searches:

```lean
#check MeasureTheory.volume_preserving_piFinSuccAbove
#check MeasureTheory.measurePreserving_piFinSuccAbove
#check MeasureTheory.MeasurePreserving.integral_comp
#check MeasureTheory.MeasurePreserving.integral_comp'
#check MeasureTheory.lintegral_prod
#check MeasureTheory.integral_prod
```

Also grep `lintegral_comp` and the implementation of `piFinSuccAbove` in the pinned Mathlib version. For the restricted box, transporting its **indicator** through the full-space equivalence is often simpler than constructing a new measure-preserving statement between restricted measures.

### ENNReal versus Bochner

**Use `lintegral` for substitution, product density, and box transport. Use Bochner for the final real asymptotic.**

That avoids repeatedly proving integrability before applying Tonelli. Establish finiteness and convert to the real integral once, at the application boundary.

For the one-dimensional power substitution, remember that “nonnegative \(g\)” also needs measurability. A useful general form uses a positive real power \(r\), with weight \(u^{r\lambda-1}\); specialise to \(r=2k\). Whether that abstraction saves work depends on the substitution API already available in your checkout.

---

## (b) The core FTC identity

Yes. Your antiderivative is right, and the endpoint \(t=z\) causes no analytic problem.

I recommend eliminating natural subtraction from the statement:

\[
\boxed{
\int_z^1 \frac{(\log t-\log z)^m}{t}\,dt
=
\frac{(-\log z)^{m+1}}{m+1}
}
\qquad(m\in\mathbb N,\ 0<z\le1).
\]

Prove this version first, then rewrite

\[
-\log(z/t)=\log t-\log z.
\]

The antiderivative is

\[
F(t)=\frac{(\log t-\log z)^{m+1}}{m+1}.
\]

The practical points are:

- derive \(t>0\) throughout the integration interval from \(z>0\);
- explicitly discharge the nonzero cast of `m + 1`;
- supply continuity/interval integrability of the derivative if the chosen FTC theorem requests it;
- use the endpoint power \(m+1>0\) to simplify \(F(z)=0\);
- keep `m = 0` in the theorem: \(0^0=1\) in the integrand is correct;
- `z = 1` is harmless, though a separate simplification branch can make the interval bookkeeping easier.

For the later `lintegral` use, add a corollary converting this nonnegative real integral to ENNReal. Here nonnegativity follows from \(z\le t\).

This is a good small standalone unit.

---

## (c) Integral identity or pushforward equality?

**Make the integral identity the primary deliverable. Add the pushforward equality afterwards if useful.**

Let

\[
\nu_\lambda
=
\left(\operatorname{vol}|_{(0,1]}\right)
.\mathrm{withDensity}\bigl(t\mapsto\operatorname{ofReal}(t^{\lambda-1})\bigr).
\]

For \(d=m+1\), the conceptual measure theorem is

\[
(\textstyle\prod_i t_i)_*(\nu_\lambda^{\otimes d})
=
\left(\operatorname{vol}|_{(0,1]}\right)
.\mathrm{withDensity}
\left(z\mapsto
\operatorname{ofReal}
\frac{z^{\lambda-1}(-\log z)^m}{m!}
\right).
\]

This is an elegant API, but proving it first adds measure packaging without helping the asymptotic application.

The identity for every measurable \(g:\mathbb R\to\mathbb R_{\ge0}^{\infty}\) is equally strong: measurable-set indicators recover measure equality. The eventual pushforward theorem should be a corollary using map-lintegral and measure extensionality.

Two conventions to fix explicitly:

- \(d\ge1\); dimension zero pushes forward to `dirac 1`, not this density.
- The density lives on \((0,1]\). Do not leave the support restriction implicit.

---

## (d) Is the general-\(\lambda\) asymptotic already present?

**No—not on the evidence supplied.**

Your `iterLogPrim` starts with a fixed quadratic primitive. It supplies arbitrary log multiplicity, not arbitrary Mellin exponent.

For \(k_i=1,h_i=0\), the equal ratio is \(\lambda=\tfrac12\). The substitution \(z=s^2\) relates the resulting density integral to the quadratic-kernel world, with the corresponding factors of \(2\). That is the special-case connection. It does not cover general \(\lambda\).

### The missing general lemma

For \(\lambda,\beta>0\) and \(m\in\mathbb N\), prove

\[
\int_0^1 z^{\lambda-1}(-\log z)^m e^{-\beta Nz}\,dz
\sim
\Gamma(\lambda)\beta^{-\lambda}N^{-\lambda}(\log N)^m.
\]

A clean proof substitutes \(t=Nz\). After normalisation, the integrand on \((0,\infty)\) is

\[
\mathbf1_{t\le N}\,
t^{\lambda-1}e^{-\beta t}
\left(1-\frac{\log t}{\log N}\right)^m.
\]

For \(N\ge e\), its absolute value is bounded by

\[
t^{\lambda-1}e^{-\beta t}(1+|\log t|)^m.
\]

That is integrable:

- near zero, absorb the log power into a small negative power, for example using \(\lambda/2>0\);
- at infinity, exponential decay wins.

Dominated convergence gives the limit; the Gamma integral identifies the constant. This lemma is useful beyond the monomial milestone and deserves its own file.

### Final statement

With \(d\ge1\), \(k_i>0\), \(\beta>0\), and

\[
\frac{h_i+1}{2k_i}=\lambda>0,
\]

the coefficient is indeed

\[
\boxed{
I_d(N)\sim
\frac{\Gamma(\lambda)\beta^{-\lambda}}
{(d-1)!\prod_i(2k_i)}
N^{-\lambda}(\log N)^{d-1}.
}
\]

An ENNReal exact reduction, followed by a real-valued asymptotic theorem, would be a strong milestone boundary.

### Estimate

At your current granularity, I would budget **roughly 9–13 new units**, not 3–4:

| Work | Approximate units |
|---|---:|
| Weighted one-dimensional power substitution | 1–2 |
| Log FTC and positive scaling/triangle helpers | 2 |
| Recursive product density | 1–2 |
| `Fin d` bridge and heterogeneous substitutions | 2–3 |
| General Gamma/log domination and asymptotic | 2 |
| Final monomial assembly | 1 |

Some helpers may collapse together if the pinned Mathlib substitution API is favourable.

---

## (e) Higher-value work—and the vanishing-order trap

### First priority: unequal-leading-term quotient theorem

Suppose your established chart theorems give

\[
Z_\phi(N)\sim C_\phi N^{-\alpha_\phi}(\log N)^{r_\phi},
\qquad
Z_1(N)\sim C_1N^{-\alpha_1}(\log N)^{r_1},
\]

with nonzero coefficients. Then prove

\[
\boxed{
\frac{Z_\phi(N)}{Z_1(N)}
\sim
\frac{C_\phi}{C_1}
N^{-(\alpha_\phi-\alpha_1)}
(\log N)^{r_\phi-r_1}.
}
\]

For Lean, initially retain the logarithmic factor as a **quotient of natural powers**. This avoids introducing integer powers just to express \(r_\phi-r_1\).

This separates two tasks:

1. **quotient calculus:** probably close to existing machinery;
2. **identification of the numerator’s first nonzero term:** potentially substantially harder.

An honest conditional theorem solving task 1 is already valuable. Instantiate it where your existing `canonA` theorems actually identify both leading terms. The supplied declarations do not establish that arbitrary “next exponent” extraction is already available.

### Crucial correction: corner vanishing need not improve the power

Consider

\[
Z_1(N)=\int_0^1\int_0^1 e^{-N x^2y^2}\,dx\,dy,
\qquad
Z_x(N)=\int_0^1\int_0^1 x\,e^{-N x^2y^2}\,dx\,dy.
\]

The observable \(x\) vanishes at the corner, but

\[
Z_1(N)\asymp N^{-1/2}\log N,
\qquad
Z_x(N)\asymp N^{-1/2}.
\]

Thus the posterior expectation decays like \(1/\log N\), **not an improved power of \(N\)**.

Geometrically, vanishing at the intersection does not force vanishing along all dominant faces. This is exactly why the face machinery matters.

Consequently:

- `yφ 0 0 = 0` can remove the leading logarithmic term;
- it does not alone force the leading \(N\)-exponent to increase;
- an observable-vanishing theorem must specify more than the corner value.

### A safe first vanishing-order theorem

Start with explicit coordinatewise divisibility:

\[
y_\phi(x,y)=x^a y^b\,\widetilde y(x,y),
\qquad \widetilde y(0,0)\ne0,
\]

plus the analytic hypotheses required by the chart theorem.

For the pure monomial model, the candidate coordinate ratios become

\[
\frac{h_1+a+1}{2k_1},
\qquad
\frac{h_2+b+1}{2k_2}.
\]

Their minimum controls the power, and equality controls whether the logarithm survives. For a nontrivial amplitude, the leading coefficient can involve face data when only one coordinate minimises.

If \(k_1=k_2=k\) and the amplitude is divisible by \(x^m y^m\), the common ratio increases by

\[
\frac{m}{2k},
\]

under the convention in question (a)—not \(m/k\). If by “order \(m\) in both variables” you instead mean a total-order condition, that does not imply this divisibility.

For signed observables, cancellation also needs attention. A nonnegative observable and a positive residual leading coefficient make the first theorem much cleaner.

Finally, a bounded observable under a positive posterior cannot have a genuinely diverging posterior expectation. A formal quotient “blow-up” alternative is valid algebraically, but in that bounded-observable setting its hypotheses must be incompatible.

### Review and sync

- **Second statement-level review:** worthwhile now, especially for files about face terms, exponent selection, and vanishing amplitudes. Review those first rather than treating the remaining 75 files uniformly.
- **Overleaf sync:** keep it pending explicit user authorisation. It is a release/integration action, not a mathematical next step.

---

## (f) My ranked next five units

I would interleave the highest-value paper corollary with the clean beginning of the monomial programme:

1. **u164 — General unequal-leading-term quotient calculus.**  
   Power/log normalisation, coefficient ratio, eventual denominator nonvanishing. Keep it independent of chart-specific indexing.

2. **u165 — Unequal-start chart posterior corollary.**  
   Instantiate only the leading-term cases already supplied by the chart API. Explicitly distinguish power decay from logarithmic decay. Do not claim arbitrary corner vanishing determines the next exponent.

3. **u166 — Log-power FTC kernel.**  
   The `m + 1` formulation above, plus its nonnegative `lintegral` corollary.

4. **u167 — Recursive ENNReal product-density theorem.**  
   Include the positive-scaling/triangle helper if it fits; otherwise split this unit rather than burying substantial transport machinery inside the induction.

5. **u168 — Weighted one-dimensional power substitution.**  
   General measurable ENNReal test function; specialise cleanly to natural monomial exponents.

Then: **Gamma/log domination → Gamma/log asymptotic → `Fin d` bridge → monomial assembly**.

The most important scope sentence for the next report is:

> General logarithmic multiplicity for the recursive quadratic chart is complete; arbitrary equal-ratio monomial charts additionally require weighted product-density transport and a general Mellin-exponent asymptotic.

And for the posterior work:

> Corner vanishing can change logarithmic multiplicity without changing the leading power; coordinatewise vanishing and face contributions determine the actual rate.
