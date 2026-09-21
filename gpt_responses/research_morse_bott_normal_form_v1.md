## Executive verdict

The exact-normal-form headline is correct, with three qualifications:

1. **Use one consistent cutoff convention.** With sampling weight \(\chi(y)e^{-tL}\), the observables in your displayed formula are \(x^\alpha y^\beta\), not \(\chi(y)x^\alpha y^\beta\). The latter give \(\chi^2\) in the numerator. Both versions identify \(H\), but their formulas differ.
2. **The temperature must be known and positive.** At an unknown temperature, the covariance identifies \(tH\), not \(H\).
3. **This is identification in fixed coordinates, with a fixed reference volume.** Loss-dependent Morse coordinates are not themselves observable coordinates.

I would make this your next positive theorem. There is also a clean, inexpensive counterexample settling the **finite polynomial rescaled-test** question negatively in dimension at least two. It does not settle the question for arbitrary finite families of nonpolynomial tests.

---

# Q1. The exact theorem and its interpretation

## 1. A clean formulation

Let \(\chi\in C_c(\mathbb R^n)\) be nonnegative and nonzero. Let \(H_j\) be continuous, symmetric positive definite on a neighborhood of \(\operatorname{supp}\chi\). Define
\[
dP_{H,t}(x,y)
=
\frac{\chi(y)e^{-t x^\top H(y)x/2}}{Z_H(t)}\,dx\,dy,
\qquad t>0.
\]

Continuity and compactness already give the required uniform ellipticity on \(\operatorname{supp}\chi\).

**Exact quadratic-bundle identification theorem.** For a fixed known \(t>0\), the following are equivalent:

* \(H_1=H_2\) on \(\{\chi>0\}\);
* for every tangential multi-index \(\beta\),
  \[
  E_{H_1,t}[y^\beta]=E_{H_2,t}[y^\beta],
  \]
  and, for every \(1\le i\le k\le r\),
  \[
  E_{H_1,t}[x_i x_k y^\beta]
  =
  E_{H_2,t}[x_i x_k y^\beta].
  \]

Thus the linear transverse observables are unnecessary: they vanish identically.

The proof is exactly the one you propose. Set
\[
A_H=\int\chi(y)\det H(y)^{-1/2}\,dy,
\qquad
d\nu_H(y)=\frac{\chi(y)\det H(y)^{-1/2}}{A_H}\,dy.
\]
Then
\[
E_{H,t}[y^\beta]=\int y^\beta\,d\nu_H,
\]
and
\[
tE_{H,t}[x_i x_k y^\beta]
=
\int y^\beta(H^{-1})_{ik}\,d\nu_H.
\]

Compact-support moment determinacy identifies the scalar measure \(\nu_H\) and the matrix-valued measure
\[
M_H=H^{-1}\nu_H.
\]
Their Radon–Nikodym ratio identifies \(H^{-1}\), initially almost everywhere and then everywhere on \(\{\chi>0\}\) by continuity.

Once \(H_1=H_2\) there, \(A_{H_1}=A_{H_2}\). **There is no remaining normalization ambiguity.**

A useful strengthening of the headline is:

> The tangential marginal and the transverse second-moment measure determine the entire exact quadratic-bundle model on the observed window.

Consequently, higher transverse moments carry no additional identifying information—not merely for \(H\), but for any expectation under this model.

### Cutoff conventions

If the fixed observable family really must be
\[
\chi(y)x^\alpha y^\beta
\]
while the base sampling weight already contains \(\chi\), then the recovered scalar and matrix measures have densities
\[
\frac{\chi^2\det H^{-1/2}}{A_H},
\qquad
\frac{\chi^2\det H^{-1/2}H^{-1}}{A_H}.
\]
Their ratio still identifies \(H^{-1}\) on \(\{\chi>0\}\). So the theorem survives unchanged in substance.

Also, adding a normal cutoff changes the exact formula only by an exponentially small tail **if that cutoff is identically one on a uniform normal neighborhood of the relevant zero set**. An arbitrary smooth normal cutoff generally changes algebraic coefficients.

## 2. What tangential observables alone identify

Tangential observables alone identify precisely \(\nu_H\). Equivalently,
\[
\frac{\det H_1^{-1/2}}{A_{H_1}}
=
\frac{\det H_2^{-1/2}}{A_{H_2}}
\quad\text{on }\{\chi>0\}.
\]

Thus they determine \(\det H\) up to one global positive factor. They do not determine the shape of \(H\).

For \(r\ge2\), even pointwise determinant-preserving changes of the Hessian field are invisible to all tangential tests. For \(r=1\), the remaining ambiguity is just a constant rescaling of the scalar Hessian field.

The most natural conceptual formulation is therefore:

> **Tangential moments identify the normalized base measure; transverse second moments identify the conditional covariance.**

Indeed,
\[
X\mid Y=y\sim N\!\left(0,t^{-1}H(y)^{-1}\right).
\]
Your theorem is an exact, moment-based reconstruction of this conditional Gaussian model.

This also explains why single-temperature identification is possible. The substantial restriction is not “one temperature”; it is “only transverse degrees zero and two.”

## 3. Coordinate-free version and SLT

Fix an ambient Riemannian metric and its volume measure. On a Morse–Bott zero manifold \(W\), write \(H_N\) for the positive normal Hessian. The leading unnormalized measure is
\[
(2\pi)^{r/2}\,
\chi\,\det(H_N)^{-1/2}\,d\mathrm{vol}_W.
\]

Normalized leading expectations see
\[
d\nu_W
=
\frac{\chi\,\det(H_N)^{-1/2}\,d\mathrm{vol}_W}
{\int_W\chi\,\det(H_N)^{-1/2}\,d\mathrm{vol}_W}.
\]

The determinant here is defined relative to the normal metric. The product involving the reference volume is the invariant object; the determinant alone is not invariant under arbitrary coordinate changes.

Writing
\[
A=\int_W\chi\,\det(H_N)^{-1/2}\,d\mathrm{vol}_W,
\]
the usual asymptotics give
\[
Z(t)\sim (2\pi)^{r/2}A\,t^{-r/2},
\]
and hence
\[
\log Z(t)
=
-\frac r2\log t+\frac r2\log(2\pi)+\log A+o(1).
\]
For free energy defined as \(-\log Z\), the signs reverse.

Thus the Morse–Bott SLT data are
\[
\lambda=r/2,\qquad \text{multiplicity}=1.
\]
Leading normalized expectations identify the normalized measure, **not \(A\)**. The latter is discarded by normalization.

## 4. General Morse–Bott losses in original coordinates

At leading order, the right statement is particularly clean:

> All leading-order ambient monomial expectations determine the normalized Morse–Bott measure as a compactly supported measure in the original ambient space.

If \(\iota:W\hookrightarrow\mathbb R^d\), they determine
\[
\iota_*\nu_W.
\]

I would call this “identification of the embedded Morse–Bott measure by its moments,” rather than “the measure pushed forward by the moments.” The pushforward is by the inclusion; the moments identify it.

With the single-cutoff convention, its support is
\[
\overline{W\cap\{\chi>0\}}.
\]
Thus on the open observation region \(\{\chi>0\}\), it identifies the embedded zero manifold, and then the determinant density up to normalization. It does **not** identify the full normal Hessian for normal rank at least two.

### The next-order object

There is a very natural next theorem. In a tubular neighborhood, let
\[
\pi(z)\in W,\qquad n(z)=z-\pi(z)\in N_{\pi(z)}W.
\]
For a smooth test endomorphism \(B\) of the normal bundle,
\[
t\,E_t\!\left[\langle n(z),B(\pi(z))n(z)\rangle\right]
\longrightarrow
\int_W\operatorname{tr}(B H_N^{-1})\,d\nu_W.
\]

Thus **leading base measure plus leading rescaled normal covariance identifies the normal Hessian field** in the general Morse–Bott case too.

Equivalently, for smooth \(f\) vanishing to first order on \(W\),
\[
tE_t[f]
\longrightarrow
\frac12\int_W
\operatorname{tr}\!\left(H_N^{-1}\operatorname{Hess}_N f\right)\,d\nu_W.
\]

This isolates the covariance term without contamination from the denominator correction or lower-order normal derivatives of the observable.

Relating this theorem back to the *original fixed monomials* needs another argument. Under a standard two-term expansion, the coefficient is a compactly supported distribution of finite order. Its values on all monomials determine it. One can then recover its principal normal second-derivative term, hence \(H_N^{-1}\nu_W\).

That is a sound route, but it needs either:

* polynomial approximation in an appropriate \(C^k\) norm, or
* moment determinacy for compactly supported distributions.

Ordinary continuous-function Stone–Weierstrass alone does not justify this step.

Finally, a terminology warning worth keeping explicit in the note: in the smooth category, beyond-all-orders data identify **infinite jets/formal germs**, not literal smooth germs; flat perturbations can be invisible.

---

# Q2. Moment determinacy in Lean

I cannot certify current Mathlib declaration availability without checking your checkout. In particular, I would not promise an existing multivariate Stone–Weierstrass corollary or a compiling 20-line proof.

But you can simplify your proposed route substantially:

> **Use the range of the `MvPolynomial` evaluation algebra homomorphism. Do not prove a separate “adjoin equals monomial span” theorem.**

## Suggested architecture

Choose a compact box \(K\) containing \(\operatorname{supp}f\). Let
\[
c_i\in C(K,\mathbb R)
\]
be the restricted coordinate maps. Evaluate multivariate polynomials at these maps:
\[
\operatorname{ev}:
\mathbb R[X_1,\dots,X_n]\longrightarrow_{\mathbb R\text{-alg}} C(K,\mathbb R).
\]

In Lean terms, the relevant construction is schematically
```lean
MvPolynomial.aeval (fun i => coordinateMap i)
```
with codomain `C(K, ℝ)`, followed by its algebra-hom range.

That range:

* contains constants;
* separates points, because the coordinate functions do;
* is therefore uniformly dense by the real Stone–Weierstrass theorem.

To prove vanishing integrals for its elements, expand a multivariate polynomial as a finite sum of monomials. You never need an independent description of an algebraic adjoin.

## A short mathematical endgame

The functional
\[
\Lambda(g)=\int_K g f
\]
is continuous in the uniform norm:
\[
|\Lambda(g)|\le \|g\|_\infty\int_K|f|.
\]
The moment assumptions imply it vanishes on polynomial restrictions, hence on all \(C(K)\). Taking \(g=f|_K\),
\[
\int f^2=0.
\]
Continuity and full support of ambient Lebesgue measure imply \(f=0\) everywhere.

A direct approximation proof avoids packaging the functional:
\[
\int f^2
=
\int f(f-p),
\qquad
\left|\int f(f-p)\right|
\le \|f-p\|_{C(K)}\int|f|.
\]

For formalization, keep the final nonnegativity/full-support argument on ambient \(\mathbb R^n\). This avoids accidental assumptions about the support of Lebesgue measure restricted to an arbitrary compact set.

## Measures versus densities

A reusable theorem for finite measures supported in a compact set would be stronger:
\[
\left(\forall\beta,\ \int y^\beta\,d\mu=\int y^\beta\,d\nu\right)
\Longrightarrow \mu=\nu.
\]

However, for your immediate Hessian theorem, the continuous-density version may be cheaper: it avoids converting back from almost-everywhere equality and needing measure-extensionality infrastructure.

The matrix-weighted differences are handled entrywise.

## Fourier route?

I would not choose it here unless your repo already has the relevant compact-support Fourier machinery.

The characteristic-function route requires proving that equality of moments yields equality of characteristic functions, typically by an absolutely convergent exponential-series argument. That adds complex integration and interchange-of-sum-and-integral obligations.

A `Measure.ext_of_charFun`-type theorem settles the **last** step, not that analytic bridge. Stone–Weierstrass is likely the shorter total development.

---

# Q3. Finite rescaled tests: a clean negative result, with a boundary

## 1. All finite polynomial families fail in dimension at least two

This can be closed negatively, even with:

* analytic losses;
* the same positive-definite quadratic part;
* a radial compact cutoff;
* exact equality at every temperature, not merely matching asymptotic series.

Let \(z=x_1+ix_2\), and let \(m\) bound the degree of your finite polynomial test family. Choose
\[
N>\max(m,2),\qquad \varepsilon\ne0,
\]
and define
\[
L_\theta(z)
=
\frac12|z|^2
+\varepsilon\,\operatorname{Re}(e^{-iN\theta}z^N)
+\varepsilon^2|z|^{2N-2}.
\]

These are globally nonnegative, with a unique nondegenerate zero at \(0\). Indeed, with \(s=\varepsilon |z|^{N-2}\),
\[
L_\theta(z)
\ge |z|^2\left(\frac12-|s|+s^2\right)
\ge \frac14|z|^2.
\]
Their Hessians at zero are all the identity, while their degree-\(N\) jets vary with \(\theta\).

Each loss is invariant under rotation through \(2\pi/N\). For any polynomial \(P\) of total degree at most \(m<N\), its average over this cyclic group is fully rotation-invariant: no nonzero angular Fourier mode of order below \(N\) survives.

With a radial cutoff, therefore,
\[
E_{L_\theta,t}[P]
\]
is independent of \(\theta\). The same is true for
\[
E_{L_\theta,t}[P(\sqrt t\,z)],
\]
because this remains a polynomial of degree at most \(m\).

Hence:

> No fixed finite family of polynomial rescaled tests identifies analytic loss germs in dimension at least two.

For a generic choice of \(\theta\), the germs are genuinely different. The example extends to higher dimensions by adding an independent positive quadratic loss in the remaining coordinates and using a suitable invariant cutoff.

This is stronger than a dimension-counting obstruction: nonlinear higher-order effects do not rescue the tests.

## 2. Do not generalize this to arbitrary finite test families

The construction applies to polynomial tests, and more generally to suitable families with bounded angular frequency. It does not establish failure for arbitrary fixed smooth nonpolynomial tests.

Those tests may contain infinitely many angular frequencies. A first-order kernel argument is insufficient because later asymptotic coefficients can encode nonlinear information about an earlier invisible perturbation.

There is also a useful dimensional warning: **finite families can work in dimension one.**

Formally, the two rescaled tests
\[
u,\qquad u^2
\]
triangularly recover a one-dimensional Taylor series about a known nondegenerate minimum. If \(a_kx^k\) is the first unknown term, its first contribution is proportional to
\[
-a_k\,\operatorname{Cov}_{G_h}(\phi(U),U^k).
\]
For odd \(k\), choose \(\phi(U)=U\); for even \(k\), choose \(\phi(U)=U^2\). The respective covariances are nonzero. The leading \(U^2\) expectation first recovers the Hessian \(h\).

Thus the clean closure is:

* **finite polynomial tests, \(d\ge2\): negative;**
* **finite tests in \(d=1\): positive examples exist;**
* **arbitrary finite nonpolynomial families in higher dimensions: not settled by this argument.**

---

# Q4. Ranked next theorems

## 1. Exact quadratic-bundle identification — highest priority

Prove the equivalence using tangential moments and transverse second moments at one known temperature.

Why first:

* It gives a genuinely non-isolated identifiability theorem.
* It uses your existing Gaussian formulas directly.
* It avoids parameter-uniform asymptotic remainders.
* It cleanly separates normalized density information from Hessian information.
* Compact moment determinacy becomes reusable infrastructure.

For efficiency, prove only the Gaussian degree-zero and degree-two formulas first. General homogeneous scaling is useful, but not necessary for the identification headline.

## 2. Finite polynomial rescaled-test nonidentifiability

Formalize the cyclic-symmetry example above.

Why second:

* It closes a precisely stated open question.
* The conclusion is exact in temperature.
* It delineates what “fixed observable family” can mean.
* It turns your linear trace-kernel picture into a nonlinear, all-orders obstruction.

The main cost is polynomial rotation/group averaging, not asymptotic analysis.

## 3. General Morse–Bott normal-covariance recovery

Prove
\[
tE_t[\langle n,Bn\rangle]
\longrightarrow
\int_W\operatorname{tr}(BH_N^{-1})\,d\nu_W.
\]

Why third:

* It transfers the exact-model insight to genuine curved Morse–Bott geometry.
* It identifies the next object after the leading Morse–Bott measure.
* It needs only leading Gaussian analysis for a quadratically vanishing observable, rather than a full all-orders expansion.

This is substantially more expensive because of tubular geometry and uniformity. I would initially state it for adapted tests, postponing the conversion to original-coordinate monomial coefficient data.

**Recommended narrative for the note:** leading tangential data identify the normalized zero-set measure; second transverse data identify the normal metric/Hessian; bounded polynomial designs still cannot identify unrestricted higher germs. That is a sharp and coherent account of what expectation values know.