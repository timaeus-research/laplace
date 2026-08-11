## A. Informal proof

### A1. Pencil identity and analytic caveats

The pointwise identity is exact. With
\[
g=L_2-L_1,\qquad L_s=L_1+s(L_2-L_1),
\]
one has
\[
\partial_s e^{-tL_s(w)}=-t\,g(w)e^{-tL_s(w)},
\]
and hence
\[
e^{-tL_1(w)}-e^{-tL_2(w)}
=t\int_0^1g(w)e^{-tL_s(w)}\,ds.
\]

No asymptotic argument is involved.

The integrated identity requires Fubini/Tonelli or absolute integrability of
\[
(s,w)\longmapsto \phi(w)g(w)e^{-tL_s(w)}.
\]
In the intended localized setting this is automatic:

- \(\phi\in C_c^\infty(U)\);
- \(L_1,L_2,g\) are continuous on a neighborhood of \(\operatorname{supp}\phi\);
- \(s\in[0,1]\);
- therefore the integrand is bounded and compactly supported in \(w\).

For the actual witness \(\phi=g\psi\), the integrand contains \(g^2\psi\), still continuous and compactly supported.

**Verdict:** watertight under the intended open-domain localization. The TeX suppresses the Fubini hypothesis, but compact support supplies it.

---

### A2. The observable \(g\psi\) and positivity

Taking \(\phi=g\psi\), with \(\psi\ge 0\), gives
\[
\Delta_t(g\psi)
=t\int_0^1\int g(w)^2\psi(w)e^{-tL_s(w)}\,dw\,ds.
\]
Every factor in the inner integral is nonnegative for \(t\ge0\). Thus
\[
\Delta_t(g\psi)\ge0.
\]

For \(s\in[0,1]\),
\[
L_s=(1-s)L_1+sL_2\le L_1+L_2
\]
provided \(L_1,L_2\ge0\). Consequently
\[
e^{-tL_s}\ge e^{-t(L_1+L_2)}
\]
and
\[
\Delta_t(g\psi)
\ge t\int g^2\psi e^{-t(L_1+L_2)}.
\]

The assumptions are used as follows:

- **Nonnegativity of \(L_1,L_2\):** needed for \(L_s\le L_1+L_2\), and to ensure the zero of \(K=L_1+L_2\) is a minimum.
- **Common zero locus:** used to ensure that at the chosen \(p\in W_0\),
  \[
  L_1(p)=L_2(p)=0,
  \]
  so \(K(p)=0\). It also implies every \(L_s\) has zero locus exactly \(W_0\).
- The common-locus assumption is not itself needed for the algebraic positivity of \(g^2\psi\).

If the zero loci differ, the theorem excludes that case. The later remark correctly explains why equality of all asymptotics would itself rule it out: a bump around a point where one loss vanishes and the other is positively bounded produces a polynomial contribution for one integral and an exponentially small one for the other.

**Verdict:** correct. The common-zero-locus assumption is stronger than what the pencil identity needs, but is exactly what makes the local sector comparison apply at every selected point.

---

### A3. Sector bound and the exponent

Let \(p=0\), let \(a=g\), and suppose the analytic germ of \(a\) is nonzero. Let \(m\) be its finite vanishing order:
\[
a(w)=P_m(w)+O(\|w\|^{m+1}),
\]
where \(P_m\) is a nonzero homogeneous polynomial of degree \(m\).

A nonzero homogeneous polynomial may vanish on large cones, so one cannot use an arbitrary spherical sector. The proof correctly chooses a good direction:

1. Since \(P_m\not\equiv0\), there is \(\theta_0\in S^{d-1}\) with
   \[
   P_m(\theta_0)\ne0.
   \]
2. By continuity, there is a fixed spherical cap \(\Omega\) around \(\theta_0\) and \(c>0\) such that
   \[
   |P_m(\theta)|\ge2c\qquad(\theta\in\Omega).
   \]
3. Uniformity of the Taylor remainder on the compact cap gives, after shrinking \(r_0\),
   \[
   |a(r\theta)|\ge c r^m
   \]
   for \(\theta\in\Omega\) and \(0<r\le r_0\).

The cap is fixed independently of \(t\), so its angular measure is a positive \(t\)-independent constant.

For
\[
K=L_1+L_2,
\]
nonnegativity and \(K(0)=0\) imply \(DK(0)=0\). Since \(K\) is \(C^2\),
\[
K(w)\le C_0\|w\|^2
\]
near \(0\).

On the annular sector
\[
\mathcal A_t
=\{r\theta:\theta\in\Omega,\ t^{-1/2}\le r\le2t^{-1/2}\},
\]
one has

- \(g^2\gtrsim r^{2m}\asymp t^{-m}\);
- \(e^{-tK}\ge e^{-4C_0}\);
- \(\operatorname{vol}(\mathcal A_t)\asymp t^{-d/2}\).

Therefore
\[
\int g^2\psi e^{-tK}\gtrsim t^{-m-d/2},
\]
and the outer pencil factor \(t\) gives
\[
\Delta_t(g\psi)\gtrsim t^{1-m-d/2}.
\]

The exponent is correct.

For \(d=0\), the spherical-cap proof does not apply, but the theorem is trivial: the parameter space is a point and a common zero forces both losses to vanish there. In the intended learning-theory setting \(d\ge1\).

**Verdict:** watertight. The possible vanishing of the leading polynomial on cones is explicitly neutralized by selecting a cap around a nonvanishing direction.

---

### A4. From local infinite-order vanishing to equality near \(W_0\)

The proof argues contrapositively. If \(g\) does not vanish on any neighborhood of \(W_0\), then not every point \(p\in W_0\) can have a neighborhood \(V_p\) on which \(g=0\). Indeed, if every point did, compactness would provide a finite subcover and hence a neighborhood of all of \(W_0\) on which \(g=0\).

Thus there is a point \(p\in W_0\) where the germ of \(g\) is nonzero. Analyticity then guarantees finite vanishing order, and the sector argument yields the contradiction.

No connectedness is required:

- equality is first obtained germwise;
- the union of the local equality neighborhoods is a neighborhood of \(W_0\);
- disconnected components cause no difficulty.

Compactness is used for the particular contradiction formulation involving one neighborhood of all of \(W_0\). Pointwise equality neighborhoods could also simply be unioned, but compactness is part of the stated local setup anyway.

**Verdict:** correct.

---

### A5. Beyond-all-orders data and the single witness

The contradiction uses only
\[
\phi=g\psi.
\]
This observable satisfies the required test-function conditions:

- \(g\) is analytic, hence smooth;
- \(\psi\in C_c^\infty\);
- therefore \(g\psi\in C_c^\infty\);
- no sign restriction is imposed on observables.

The hypothesis quantifies over every \(\phi\), so it applies to this loss-dependent witness. There is no requirement that observables be chosen independently of the candidate losses.

The lower bound
\[
\Delta_t(g\psi)\ge C t^\gamma,\qquad
\gamma=1-m-\frac d2,
\]
contradicts decay faster than every negative integer power: choose \(N>-\gamma\).

There is a minor notational looseness in the appendix where the contradiction is described using \(N=m+d/2\), potentially nonintegral when \(d\) is odd. If the convention quantifies only over \(N\in\mathbb N\), one should instead choose any integer \(N>m+d/2-1\). The formal proof does exactly that. This does not affect the theorem.

Also, the note sometimes defines \(o(t^{-\infty})\) as \(O(t^{-N})\) for every \(N\), while the Lean endpoint uses little-\(o\) for every \(N\). These are equivalent for this purpose: \(O(t^{-(N+1)})\) implies \(o(t^{-N})\).

**Verdict:** correct, with only a minor notation issue.

---

### A6. Boundary and localization

The sector must lie inside the domain of integration and inside the region where:

- \(L_1,L_2\) are analytic;
- \(K\le C_0\|w-p\|^2\);
- \(\psi=1\).

Because the localization domain \(U\) is open and \(p\in U\), one can choose a ball around \(p\) compactly contained in \(U\), then choose \(\psi\) supported in that ball. For sufficiently **large** \(t\), not small \(t\), the \(t^{-1/2}\)-sector lies inside it.

The TeX proof says to choose \(r_0\) and then \(t\) large enough that \(2t^{-1/2}\le r_0\), which is the required check.

A literal formulation in which \(W_0\) could touch the boundary of the integration region would need an interior-point or relative-sector argument. The phrase “localized as above” rules that out in the intended setup.

**Verdict:** correct under the intended open localization.

---

## B. Formal proof

### B1. What the main Lean theorems actually prove

#### 1. Pencil identities

`exp_sub_exp_pencil` proves, for arbitrary real \(t,x,y\),
\[
e^{-tx}-e^{-ty}
=t\int_0^1(y-x)e^{-t(x+s(y-x))}\,ds.
\]

`exp_pencil_identity` substitutes \(x=L_1(w)\), \(y=L_2(w)\).

`pencil_identity_integrated` proves the integrated one-dimensional identity under an explicit absolute-integrability hypothesis on the product \([0,1]\times\mathbb R\).

`pencil_identity_integrated_measure` proves the same over an arbitrary s-finite measure space. This is what allows the multivariate proof to use Lebesgue measure on \(\iota\to\mathbb R\).

`exp_pencil_ge` and `exp_pencil_ge_scalar` prove
\[
e^{-t(L_1+L_2)}
\le e^{-t(L_1+s(L_2-L_1))}
\]
for \(t\ge0\), \(s\in[0,1]\), and nonnegative potentials.

These statements match the informal proof exactly.

---

#### 2. One-dimensional sector bound

`sector_window_lower_bound` assumes on \([0,r_0]\):
\[
K(w)\le C_0w^2,\qquad c\,w^m\le |a(w)|.
\]
It proves a lower bound on the window \([u,2u]\).

`sector_lower_bound` sets \(u=(\sqrt t)^{-1}\) and proves
\[
c^2e^{-4C_0}t^{-m-1/2}
\le
\int_{[t^{-1/2},2t^{-1/2}]}
a(w)^2e^{-tK(w)}\,dw.
\]

This is precisely the one-dimensional sector estimate needed. It assumes the finite-order lower bound rather than analyticity directly.

---

#### 3. Multivariate sector bound

`sector_window_lower_bound_multi` works on \(\iota\to\mathbb R\), with the sup norm and Lebesgue measure. It assumes a measurable finite-volume set \(S\), and lower bounds \(a(u x)\) on the scaled set \(uS\).

`sector_lower_bound_multi` proves
\[
\operatorname{vol}(S)c^2e^{-4C_0}
t^{-m-d/2}
\le
\int_{t^{-1/2}S}a(w)^2e^{-tK(w)}\,dw,
\]
where \(d=\operatorname{card}\iota\).

The theorem itself does not require \(\operatorname{vol}(S)>0\), so in isolation its lower bound could be zero. That is harmless because `leading_part_scaled_set` later constructs an \(S\) of explicitly nonzero volume.

---

#### 4. Composite identifiability bounds

`pencil_difference_lower_bound` proves in one dimension
\[
c^2e^{-4C_0}\,t\,t^{-m-1/2}
\le
\int (L_2-L_1)\psi
\left(e^{-tL_1}-e^{-tL_2}\right).
\]

`pencil_difference_lower_bound_multi` proves the analogous
\[
\operatorname{vol}(S)c^2e^{-4C_0}\,
t\,t^{-m-d/2}
\le
\int (L_2-L_1)\psi
\left(e^{-tL_1}-e^{-tL_2}\right).
\]

They require:

- global nonnegativity of \(L_1,L_2\);
- a local quadratic upper bound for \(L_1+L_2\);
- a bump \(\psi\ge0\), equal to \(1\) on the relevant ball;
- explicit integrability hypotheses;
- finite-order growth of \(L_2-L_1\) on the selected window.

The sign and exponent match the note.

---

#### 5. Analytic or leading-part factoring

`analytic_growth_lower_bound` is one-dimensional. Given an analytic \(a\) at \(0\) with finite analytic order, it produces
\[
c\,w^m\le |a(w)|
\]
on a one-sided interval \([0,r_0]\), with \(c>0\).

`leading_part_scaled_set` is multivariate. It assumes:

- a continuous homogeneous leading part \(P\);
- a point \(x_0\) with \(P(x_0)\ne0\) and \(\|x_0\|=3/2\);
- a Taylor remainder estimate
  \[
  |a(x)-P(x)|\le C\|x\|^{m+1}.
  \]

It then constructs a fixed positive-volume set \(S\) on which
\[
c\,u^m\le |a(ux)|.
\]

This handles zeros of \(P\) on other cones correctly.

`analytic_remainder_bound` derives the remainder estimate from a formal power series, assuming all diagonal terms below degree \(m\) vanish.

`analytic_pencil_difference_lower_bound_multi` combines those ingredients, but it still assumes a nonvanishing diagonal degree-\(m\) value at a normalized \(x_0\).

---

#### 6. Turnkey integrability

The one-dimensional and multivariate turnkey files prove the compact-support integrability obligations from:

- global continuity of \(L_1,L_2\);
- continuity and compact support of \(\psi\).

This is mathematically stronger in domain assumptions than the local note: the Lean functions are defined and continuous on all of \(\mathbb R^d\). Since every integrand contains \(\psi\), only values near its support matter, but the reduction from locally defined losses to globally defined continuous functions is not formalized here.

---

#### 7. Rapid-decay contradiction

`lower_bound_not_superpolynomial` proves that an eventual lower bound
\[
\Delta(t)\ge\kappa t^\gamma,\qquad \kappa>0,
\]
is incompatible with
\[
\Delta=o(t^{-N})
\]
for every \(N\in\mathbb N\).

`analytic_pencil_difference_not_superpolynomial` proves that, under the multivariate analytic/Taylor hypotheses,
\[
\Delta(t)
=
\int (L_2-L_1)\psi
\left(e^{-tL_1}-e^{-tL_2}\right)
\]
cannot decay faster than every negative power.

This checks the quantitative contradiction, not the full neighborhood-equality theorem.

---

### B2. Hypothesis audit of the final theorem

Yes, the power series is centered at the interesting point \(0\). This is encoded by
```lean
HasFPowerSeriesOnBall (fun w ↦ L₂ w - L₁ w) p 0 r
```
and by all local estimates being around \(0\).

The note-level proof selects an arbitrary \(p\in W_0\) and translates coordinates. That translation step is not part of `analytic_pencil_difference_not_superpolynomial`.

The theorem also does not explicitly assume \(L_1(0)=L_2(0)=0\). Instead this follows from:

- global nonnegativity;
- the bound
  \[
  L_1(w)+L_2(w)\le C_0\|w\|^2
  \]
  at \(w=0\).

Thus the vanishing at the center is encoded correctly.

The forbidden decay concerns the exact proxy
\[
\Delta(t)
=\int g\psi(e^{-tL_1}-e^{-tL_2}),
\]
which is exactly the difference of the two unnormalized integrals for the observable \(\phi=g\psi\), provided the two separate compactly supported integrals are integrable. That final identification is mathematically immediate but is not packaged into the endpoint theorem as “equality of expansion families implies contradiction.”

Likewise, the endpoint formalizes little-\(o\) decay for every integer power, not equality of power-log asymptotic coefficient families. The semantic implication from identical full expansions to this rapid-decay statement remains outside the endpoint.

---

### B3. Vanishing cones and existence of \(x_0\)

`leading_part_scaled_set` handles nontrivial vanishing cones correctly once supplied with one point \(x_0\) satisfying \(P(x_0)\ne0\). It takes a closed ball around \(x_0\), uses continuity to keep \(|P|\) bounded below there, and obtains a positive-volume scaled set.

However, the existence of such an \(x_0\) is **hypothesized**, not proved in the supplied chain.

To derive it from a nonzero analytic germ one still needs to prove:

1. there is a least degree \(m\) with a nonzero power-series coefficient;
2. the associated symmetric multilinear form has a nonzero diagonal evaluation;
3. a nonzero direction can be positively rescaled to norm \(3/2\).

The second point uses polarization over \(\mathbb R\). The third is elementary. None is mathematically problematic, but these selections are not in the displayed corpus.

The normalization \(\|x_0\|=3/2\) is harmless for \(d\ge1\). In dimension zero no such point exists; that case is trivial at the note level but not covered by this formal endpoint.

---

### B4. Uncomposed steps between the corpus and the note-level theorem

The supplied files do **not** compose directly into the exact statement of Theorem `thm:singular`. The following steps remain semantic or external:

1. **Negating neighborhood equality.**  
   From \(L_1\ne L_2\) on every neighborhood of \(W_0\), select \(p\in W_0\) where the germ of \(g=L_2-L_1\) is nonzero. This uses compactness as in the TeX proof.

2. **Translation to the origin.**  
   Replace \(w\) by \(w-p\) and identify \(\mathbb R^d\) with a Lean space \(\iota\to\mathbb R\).

3. **Analytic power-series extraction.**  
   Produce `HasFPowerSeriesOnBall` for \(g\) at the translated origin.

4. **Least nonzero degree.**  
   Choose \(m\), prove all lower diagonal terms vanish, and prove the degree-\(m\) diagonal polynomial is nonzero somewhere.

5. **Normalize the direction.**  
   Produce \(x_0\) with \(\|x_0\|=3/2\).

6. **Quadratic upper bound.**  
   Derive
   \[
   L_1(w)+L_2(w)\le C_0\|w\|^2
   \]
   from \(C^2\)-regularity, nonnegativity, and common vanishing at the center.

7. **Bump construction.**  
   Choose a smooth, nonnegative, compactly supported \(\psi\) equal to \(1\) on a sufficiently small ball.

8. **Local-to-global function issue.**  
   The Lean turnkey theorem expects globally defined continuous and globally nonnegative functions. The note assumes losses only on a neighborhood. One must either:
   - state the formal theorem locally, or
   - extend the losses outside a compact neighborhood while preserving the properties needed on \(\operatorname{supp}\psi\).

9. **Observable membership.**  
   Verify \(\phi=g\psi\in C_c^\infty\). This is elementary but not part of the endpoint theorem.

10. **Expansion-family bridge.**  
    Use equality of the unnormalized expansion families to conclude
    \[
    \int \phi e^{-tL_1}-\int\phi e^{-tL_2}
    \]
    decays faster than every power.

11. **Integral rewriting.**  
    Identify that difference with the single Lean integral
    \[
    \int \phi(e^{-tL_1}-e^{-tL_2}).
    \]

12. **Final germ/neighborhood conclusion.**  
    Convert the contradiction into equality of the germ at every relevant point, then combine the local equality neighborhoods into a neighborhood of \(W_0\).

These are routine mathematical reductions, but the footnote’s assertion that “what remains outside Lean is only the reduction to the single observable \(g\psi\)” is too strong for the corpus shown. More remains outside Lean than that sentence admits.

---

### B5. Sign and normalization conventions

There is no sign error.

The TeX defines
\[
g=L_2-L_1,\qquad
\Delta_t(\phi)
=\int\phi(e^{-tL_1}-e^{-tL_2}),
\]
and proves
\[
\Delta_t(\phi)
=t\int_0^1\int \phi g e^{-tL_s}.
\]
With \(\phi=g\psi\), this becomes positive.

Lean uses exactly the same orientation:
```lean
Real.exp (-(t * L₁ w)) - Real.exp (-(t * L₂ w))
```
and amplitude
```lean
L₂ w - L₁ w
```.
The outer factor \(t\) is present.

The formal endpoint concerns unnormalized integrals only. It does not accidentally divide by a partition function, and it does not establish the normalized theorem.

---

## C. Verdict

### Informal theorem

**Correct as stated under the intended localization conventions.**

The proof has no substantive mathematical hole. Its necessary interpretation is:

- the integration domain is an open neighborhood containing \(W_0\) in its interior;
- all test functions are compactly supported there;
- the minimum values have been matched at \(0\);
- \(d\ge1\), with \(d=0\) treated trivially.

The only defects are presentational:

1. Fubini/integrability is suppressed but follows from compact support.
2. The appendix’s choice of an exact exponent \(N=m+d/2\) should be replaced by a sufficiently large integer if \(N\) is understood to range over \(\mathbb N\).
3. The domain/localization assumptions should be stated more explicitly in the theorem itself.

None yields a counterexample.

### Formal corpus

The machine-checked core is substantial and sound:

- exact pencil identity;
- positivity comparison along the pencil;
- one- and multi-dimensional sector bounds;
- construction of a positive-measure good sector from a nonzero leading homogeneous part;
- compact-support integrability;
- the quantitative lower bound
  \[
  \Delta_t(g\psi)\gtrsim t^{1-m-d/2};
  \]
- contradiction with superpolynomial decay.

What is **not** machine-checked by the supplied endpoint is the full theorem
\[
\text{equality of all unnormalized expansion families}
\Longrightarrow
L_1=L_2\text{ near }W_0.
\]

#### Severity ranking

1. **Moderate formalization-coverage gap:** the note-level theorem is not a direct theorem in the supplied corpus. Point selection, translation, least Taylor degree, direction selection, local-to-global reduction, the expansion-family bridge, and final neighborhood assembly remain outside the shown Lean chain.

2. **Moderate documentation overclaim:** the footnote saying only the choice of \(p\) and \(\psi\) remains outside Lean understates the missing composition steps.

3. **Low hypothesis mismatch:** the formal turnkey theorem assumes globally defined continuous and globally nonnegative losses, whereas the note is local. Compact support makes the reduction straightforward, but it is not formalized.

4. **Low edge-case omission:** the normalized direction \(\|x_0\|=3/2\) excludes the zero-dimensional case, which is trivial separately.

There is no detected flaw in the quantitative Lean argument itself. The corpus verifies the hard analytic inequality underlying `thm:singular`; it does not, as presented, verify the entire theorem statement end to end.