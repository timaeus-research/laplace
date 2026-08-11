Let
\[
q=t^{-1/2},\qquad D=R+2.
\]
The clean comparison statement is not a fixed absolute estimate, but the scale-sensitive one
\[
\langle x^s\rangle^{L}_{q^{-2}}
-
\langle x^s\rangle^{P}_{q^{-2}}
=o\!\left(q^{s+D-2}\right)
=o\!\left(q^{s+R}\right),
\tag{*}
\]
whenever \(P\) has the same \(D\)-jet as \(L\), both have a positive quadratic lower bound, and \(P\) is globally confining. For \(s=2\), this is exactly
\[
o(q^{R+2})=o(t^{-1-R/2}),
\]
and for larger \(s\) it is stronger. This should be the main C3 interface.

## 1. Moving split

The split
\[
|x|\le t^{-2/5}
\qquad\Longleftrightarrow\qquad
|y|=|x|/q\le t^{1/10}
\]
is sufficient for every fixed finite \(R\). It need not depend on \(R\).

More generally, one can use
\[
|x|\le t^{-1/2+\varepsilon}
\]
with any fixed sufficiently small \(\varepsilon>0\). The choice \(\varepsilon=1/10\) has two useful properties:

1. On the complement,
   \[
   t x^2\ge t^{2\varepsilon}=t^{1/5},
   \]
   so the tails are \(O(e^{-ct^{1/5}})\), hence smaller than every power of \(t^{-1}\).

2. For a Taylor remainder of order \(m\ge3\),
   \[
   t|x|^m
   \le t^{1-m(1/2-\varepsilon)}.
   \]
   With \(\varepsilon=1/10\), this is \(t^{1-2m/5}\), which tends to zero for every \(m\ge3\).

Thus the fixed \(2/5\) split works at arbitrary finite order.

The important bookkeeping point is that one must not estimate the entire inner integral merely by the supremum of \(t|L-T|\) on the moving interval. That loses too many powers as \(R\) grows. Retain the factor \(|x|^m\) inside the Gaussian integral:
\[
|e^{-tL}-e^{-tP}|
\lesssim t\,|L-P|\bigl(e^{-tL}+e^{-tP}\bigr).
\]
If
\[
L(x)-P(x)=o(|x|^D),
\]
then, for the unnormalized \(s\)-th moment,
\[
\int x^s(e^{-tL}-e^{-tP})\,dx
=o\!\left(
t\int |x|^{s+D}e^{-ct x^2}\,dx
\right)
=o\!\left(t^{-(s+D-1)/2}\right).
\tag{1}
\]
Similarly,
\[
Z_L(t)-Z_P(t)
=o\!\left(t^{-(D-1)/2}\right).
\tag{2}
\]
Since \(Z_L,Z_P\asymp t^{-1/2}\) and the unnormalized \(s\)-th moments are \(O(t^{-(s+1)/2})\), quotient subtraction gives
\[
\langle x^s\rangle_t^L-\langle x^s\rangle_t^P
=o\!\left(t^{-(s+D-2)/2}\right),
\]
which is \((*)\).

Therefore:

- Taylor degree \(D=R+2\) already suffices.
- The degree \(R+4\) truncation suggested in the question is harmless but overkill.
- With a degree-\(R+4\) truncation and an \(O(|x|^{R+5})\) remainder, the comparison is much stronger than needed.
- The moving radius need not be changed, but the proof must integrate the Taylor power rather than replace it by its boundary value.

A Lean proof may actually be cleaner if the inner Taylor estimate is performed on a fixed small ball and scaling/dominated estimates are used there; the moving split is chiefly convenient for making the outer region manifestly superpolynomial.

## 2. Stabilizing the Taylor polynomial

### Required stabilizer degree

Take the degree-\(D\) Taylor polynomial
\[
T_D(x)=a_2x^2+\sum_{j=3}^D a_jx^j,
\qquad a_2>0,
\]
and set
\[
P(x)=T_D(x)+d x^M,
\]
where \(M\) is even and
\[
M>D=R+2.
\tag{3}
\]

The condition is not merely \(M>R\). In the scaled profile,
\[
q^{-2}P(qy)
=
a_2y^2+\sum_{j=3}^D a_jq^{j-2}y^j+dq^{M-2}y^M.
\]
The stabilizer first appears at rung \(M-2\). To keep every rung \(0,\dots,R\) unchanged, one needs
\[
M-2>R,
\]
which is exactly \(M>R+2\).

The smallest convenient choice is
\[
M=\text{the least even integer strictly larger than }D.
\]
Equivalently,
\[
M=
\begin{cases}
D+2,&D\text{ even},\\
D+1,&D\text{ odd}.
\end{cases}
\]
If you retain a degree-\(R+4\) Taylor polynomial instead, then \(M\) must be the least even integer strictly larger than \(R+4\), not merely an even integer at least \(R+4\).

### Comparison after stabilization

Because \(M>D\),
\[
dx^M=o(|x|^D),
\]
and hence
\[
L(x)-P(x)
=
\bigl(L(x)-T_D(x)\bigr)-dx^M
=o(|x|^D).
\]
Consequently the master comparison \((*)\) still applies:
\[
\langle x^s\rangle^L_{q^{-2}}
-
\langle x^s\rangle^P_{q^{-2}}
=o(q^{s+R}).
\]

Directly, the stabilizer alone affects the normalized \(s\)-th moment at order
\[
O(q^{s+M-2}).
\]
Since \(M-2>R\),
\[
q^{s+M-2}=o(q^{s+R}).
\]
Thus it cannot alter any C1 rung through \(R\).

### A Lean-friendly explicit choice of \(d\)

Avoid defining \(d\) through a global supremum if possible. A coefficient-wise construction is more elementary.

Write
\[
B=\sum_{j=3}^D |a_j|.
\]
Choose \(0<\rho\le1\) so that
\[
B\rho\le \frac{a_2}{2}.
\]
For example, with a harmless branch for \(B=0\),
\[
\rho=\min\left(1,\frac{a_2}{2(B+1)}\right)
\]
works. Then, for \(|x|\le\rho\),
\[
\left|\sum_{j=3}^D a_jx^j\right|
\le B|x|^3
\le \frac{a_2}{2}x^2,
\]
so
\[
T_D(x)\ge \frac{a_2}{2}x^2.
\]

For \(|x|\ge\rho\) and \(j<M\),
\[
|x|^j\le \rho^{j-M}|x|^M.
\]
Therefore choose
\[
d\ge \sum_{j=3}^D |a_j|\rho^{j-M}.
\tag{4}
\]
Then on \(|x|\ge\rho\),
\[
\sum_{j=3}^D a_jx^j+d x^M\ge0,
\]
and hence
\[
P(x)\ge a_2x^2.
\]
Combining the two regions gives the global envelope
\[
P(x)\ge \frac{a_2}{2}x^2
\qquad\text{for all }x.
\tag{5}
\]

This construction uses only finite sums, absolute values, powers, `min`, and elementary case splits at \(|x|=\rho\). It should be substantially easier in Lean than compactifying \(\mathbb R\), taking a supremum of \(-T_D(x)/x^M\), and proving it finite.

If the existing polynomial core needs only a weaker profile envelope than (5), this construction still provides it.

## 3. C2–C5 stages

Here is the dependency order I would use.

### C2 — Local quadratic/Taylor and tail package

**Purpose:** Package all analytic estimates needed by the comparison theorem, without mentioning jet recovery.

The central Lean-flavored statements should be:

#### C2.1 Peano remainder

For \(D\ge2\), if \(L\) is \(C^D\) near \(0\), then its degree-\(D\) Taylor polynomial \(T_D\) satisfies
```lean
Tendsto (fun x => (L x - T_D x) / |x| ^ D)
  (𝓝[≠] 0) (𝓝 0)
```
or an equivalent epsilon estimate:
```lean
∀ ε > 0, ∀ᶠ x in 𝓝 0,
  |L x - T_D x| ≤ ε * |x| ^ D
```

The epsilon formulation will probably compose better with integral bounds.

#### C2.2 Stabilized Taylor polynomial

Given \(a_2>0\), \(D\ge2\), and an even \(M>D\), construct \(d\ge0\) such that
```lean
P x = T_D x + d * x ^ M
```
satisfies:

```lean
∀ x, cP * x^2 ≤ P x
```
for some `cP > 0`, and
```lean
∀ j ≤ D, polynomialCoeff P j = polynomialCoeff T_D j
```
or the corresponding coefficient-vector equality.

Also prove
```lean
Tendsto (fun x => (L x - P x) / |x| ^ D)
  (𝓝[≠] 0) (𝓝 0)
```
using \(M>D\).

#### C2.3 Gaussian-scale integral bounds

For \(a>0\), \(k\in\mathbb N\),
```lean
∫ x, |x|^k * exp (-q⁻² * a * x^2) ∂x = O(q^(k+1))
```
as \(q\to0^+\), or at least upper bounds of this order.

You likely do not need the exact Gamma-function constant. A scaling substitution plus a finite constant
\[
C_{k,a}=\int |y|^k e^{-ay^2}\,dy
\]
is enough.

#### C2.4 Partition lower and moment upper bounds

For every admissible potential \(K\),
```lean
Z K q ≍ q
```
in the one-sided sense actually needed:
```lean
C₀ * q ≤ Z K q
```
for small positive \(q\), and
```lean
|A_s K q| ≤ C_s * q^(s+1)
```
for the unnormalized monomial integral.

#### C2.5 Superpolynomial tails

For a fixed small \(\rho>0\), or for the moving radius \(q^{4/5}\),
```lean
q ^ (-N) *
  ∫ x in {x | movingRadius q ≤ |x|}, |x|^s * exp (-q⁻² * K x)
  ⟶ 0
```
for every fixed \(N,s\).

For \(L\), integrate only over \(U\); for the stabilized polynomial \(P\), integrate over \(\mathbb R\).

---

### C3 — Normalized local Taylor comparison

This is the main analytic bridge and should be stated independently of Taylor polynomials.

Let \(K_1,K_2\) satisfy:

- \(K_i(0)=0\);
- common local/global quadratic lower bounds;
- suitable integrability;
- \(K_1-K_2=o(|x|^D)\) at \(0\).

First prove the two unnormalized estimates:

```lean
theorem partitionFunction_sub_isLittleO :
  (Z K₁ - Z K₂) =o[atTop] fun t => t ^ (-(D - 1) / 2)
```

and, for the \(s\)-th numerator,
```lean
theorem monomialIntegral_sub_isLittleO :
  (A_s K₁ - A_s K₂) =o[atTop]
    fun t => t ^ (-(s + D - 1) / 2)
```

Preferably formulate them in \(q\)-space:
```lean
(Zq K₁ q - Zq K₂ q) = o(q^(D-1))
```
and
```lean
(Aq_s K₁ q - Aq_s K₂ q) = o(q^(s+D-1)).
```

Then prove the quotient theorem:

```lean
theorem normalizedMoment_sub_isLittleO
    (hjet : K₁ x - K₂ x = o(|x|^D)) :
  moment K₁ s q - moment K₂ s q = o(q^(s + D - 2))
```

This is the exact statement wanted downstream.

For \(D=R+2\):
```lean
moment K₁ s q - moment K₂ s q = o(q^(s+R)).
```

This stage is the **single hardest one**. The main sources of complexity are:

- two different domains, \(U\) and \(\mathbb R\);
- making the exponential mean-value estimate usable while preserving the factor \(|x|^D\);
- denominator lower bounds;
- quotient bookkeeping;
- filters restricted to \(q\to0^+\);
- tail estimates strong enough to discard the nonlocal parts uniformly at any requested polynomial rate.

Everything after C3 should mostly be interface adaptation.

---

### C4 — Taylor/stabilizer-to-C1 adapter

Fix \(R\), set \(D=R+2\), and choose the least even \(M>D\).

For each \(L_\nu\):

1. construct \(T_{\nu,D}\);
2. construct
   \[
   P_\nu=T_{\nu,D}+d_\nu x^M;
   \]
3. prove the polynomial profile-envelope assumptions required by the existing core;
4. prove equality of coefficients through degree \(D\);
5. apply C3:
   \[
   \langle x^s\rangle^{L_\nu}_{q^{-2}}
   -
   \langle x^s\rangle^{P_\nu}_{q^{-2}}
   =o(q^{s+R}).
   \tag{6}
   \]

The final C4 theorem should directly expose the C1-compatible scaled data. If C1 uses
\[
F_s(q)=q^{-2}\langle x^s\rangle_{q^{-2}},
\]
then (6) gives
\[
F_s^{L_\nu}(q)-F_s^{P_\nu}(q)
=o(q^{s+R-2}).
\]
For \(s=2+r\),
\[
F_{2+r}^{L_\nu}-F_{2+r}^{P_\nu}
=o(q^{r+R}).
\]
Hence, for \(0\le r\le R\),
\[
q^{-r}
\left(F_{2+r}^{L_\nu}-F_{2+r}^{P_\nu}\right)\to0.
\tag{7}
\]

A useful final statement would look schematically like:

```lean
theorem stabilizedTaylor_c1_approx
    (hr : r ≤ R) :
  Tendsto
    (fun q =>
      q⁻¹ ^ r *
        (F (L := L) (2+r) q - F (L := P) (2+r) q))
    (𝓝[>] 0) (𝓝 0)
```

with a separate unscaled statement for \(s=2\), if that is how C1 is shaped.

C4 should also contain the triangle-inequality transfer:

```lean
C1DataVanish L₁ L₂ R → C1DataVanish P₁ P₂ R
```

using
\[
P_1-P_2=(P_1-L_1)+(L_1-L_2)+(L_2-P_2).
\]

---

### C5 — Finite-order smooth recovery theorem

Apply `nondegenerateJet_recovery_stable` to \(P_1,P_2\). It gives equality of:

- the quadratic coefficient / \(\lambda\);
- every polynomial coefficient through rung \(R\), i.e. through degree \(R+2=D\).

Then remove the stabilizers using \(M>D\), and identify Taylor coefficients with derivatives of the original smooth losses.

The final theorem should have approximately the following shape:

```lean
theorem smooth_nondegenerateJet_recovery_finite
    (R : ℕ)
    (hL₁ : SmoothAdmissible L₁ U)
    (hL₂ : SmoothAdmissible L₂ U)
    (h2 :
      Tendsto
        (fun t => t * (moment L₁ 2 t - moment L₂ 2 t))
        atTop (𝓝 0))
    (hr :
      ∀ r ≤ R,
        Tendsto
          (fun t =>
            t ^ (1 + (r : ℝ) / 2) *
              (moment L₁ (2+r) t - moment L₂ (2+r) t))
          atTop (𝓝 0)) :
    ∀ k, 2 ≤ k → k ≤ R+2 →
      iteratedDeriv k L₁ 0 = iteratedDeriv k L₂ 0
```

Depending on the exact normalization in C1, the \(r=0\) case may subsume `h2`; retain the separate base hypothesis if that matches the stable interface.

The logical dependency is:

\[
\boxed{\text{C2 estimates and stabilizer}}
\longrightarrow
\boxed{\text{C3 normalized comparison}}
\longrightarrow
\boxed{\text{C4 C1 adapter}}
\longrightarrow
\boxed{\text{C5 finite smooth recovery}}.
\]

## Recommended truncation choices

For the smallest proof burden:

- Taylor degree:
  \[
  D=R+2.
  \]
- Stabilizer degree:
  \[
  M=\text{least even integer strictly greater than }D.
  \]
- Comparison target:
  \[
  \langle x^s\rangle^L-\langle x^s\rangle^P
  =o(q^{s+R}).
  \]
- Moving split, if retained:
  \[
  |x|\le q^{4/5}=t^{-2/5}.
  \]

This is exactly strong enough for all C1 rungs through \(R\), does not request unnecessary derivatives, and ensures the stabilizer is invisible at every recovered degree.