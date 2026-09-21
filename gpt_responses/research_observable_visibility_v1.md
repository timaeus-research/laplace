Your Hermite criterion is correct, but two qualifications matter:

1. **Covariance discards the constant chaos.** For even \(k\), this creates an exception when \(m<2\).
2. **The Hermite components of a homogeneous polynomial are not independent.** The clean description of the kernel is by iterated Gaussian traces; a homogeneous complement is given by Fischer decomposition, rather than by simply selecting low Hermite degrees.

Here is an exact statement and a Hermite-free formalisation route.

## 1. Exact kernel and dimension theorem

Write
\[
C=H^{-1},\qquad
\Delta_C=\sum_{a,b}C_{ab}\partial_a\partial_b,\qquad
q(x)=x^\top C^{-1}x.
\]
Let
\[
h_j=\dim\mathcal H_j=\binom{d+j-1}{j},
\]
with \(h_j=0\) for \(j<0\). Assume \(d\ge1\).

For \(k\ge1\), define the set of detectable chaos degrees
\[
J_{k,m}=\{j:1\le j\le \min(k,m),\ j\equiv k\pmod2\}.
\]

### Theorem: visibility equals an iterated trace

If \(J_{k,m}\ne\varnothing\), put
\[
s=\max J_{k,m},\qquad r=\frac{k-s}{2}.
\]
Then
\[
\boxed{
\ker\left[Q\in\mathcal H_k\longmapsto
  \bigl(\operatorname{Cov}_\gamma(x^\alpha,Q)\bigr)_{|\alpha|\le m}
\right]
=
\ker\left(\Delta_C^r:\mathcal H_k\to\mathcal H_s\right).
}
\]

The trace map \(\Delta_C^r\) is surjective. Consequently,
\[
\boxed{\dim(\text{visible quotient})=h_s,\qquad
       \dim(\text{invisible subspace})=h_k-h_s.}
\]

If \(J_{k,m}=\varnothing\), the entire \(\mathcal H_k\) is invisible.

Degree \(k=0\) is always entirely invisible to covariance.

Thus, for positive degrees:

| Tests | Degree \(k\) | Visible dimension |
|---|---:|---:|
| \(m=0\) | all \(k\) | \(0\) |
| \(m=1\) | odd \(k\) | \(d\) |
| \(m=1\) | even \(k\) | \(0\) |
| \(m\ge2\) | \(k\le m\) | \(h_k\) |
| \(m\ge2\) | \(k>m,\ k\equiv m\pmod2\) | \(h_m\) |
| \(m\ge2\) | \(k>m,\ k\not\equiv m\pmod2\) | \(h_{m-1}\) |

In particular, for fixed \(m\ge2\), the visible dimension at high jet orders alternates between two fixed values.

### Relation to your Hermite statement

If \(\Pi_j\) denotes projection onto Gaussian chaos degree \(j\), then exactly
\[
Q\text{ invisible}
\iff
\Pi_jQ=0\quad(1\le j\le m).
\]
Also, for \(Q\in\mathcal H_k\),
\[
\Pi_jQ
=
\frac{1}{2^r r!}\,
\mathcal W_C(\Delta_C^rQ),
\qquad r=\frac{k-j}{2},
\]
when \(j\le k\) and \(j\equiv k\pmod2\). Here
\[
\mathcal W_C=e^{-\Delta_C/2}
\]
is the finite polynomial “Wick transform.”

Vanishing of the largest tested parity-compatible component forces all smaller ones to vanish, because they are further traces. This explains why the rank is \(h_s\), not a sum of dimensions of independent chaos spaces.

A suitable slogan is:

> **Monomials of degree at most \(m\) identify a homogeneous degree-\(k\) jet precisely through its largest parity-compatible Gaussian trace of positive degree at most \(m\).**

For \(m\ge2\), you may equivalently say:

> **They resolve the degree-\(k\) jet modulo its homogeneous directions supported in Gaussian chaos degrees greater than \(m\).**

The qualification \(m\ge2\) removes the constant-chaos exception.

## 2. A homogeneous decomposition and the dimension sum

Define the \(C\)-harmonic homogeneous polynomials
\[
\mathscr Y_j^C=\ker(\Delta_C:\mathcal H_j\to\mathcal H_{j-2}).
\]
Weighted Fischer decomposition gives
\[
\mathcal H_k
=
\bigoplus_{\substack{0\le j\le k\\j\equiv k\ (2)}}
q^{(k-j)/2}\mathscr Y_j^C,
\qquad
\dim\mathscr Y_j^C=h_j-h_{j-2}.
\]

When \(s\) exists, the invisible space is exactly
\[
\boxed{
\bigoplus_{\substack{s<j\le k\\j\equiv k\ (2)}}
q^{(k-j)/2}\mathscr Y_j^C.
}
\]
A corresponding homogeneous visible complement is
\[
\bigoplus_{\substack{0\le j\le s\\j\equiv k\ (2)}}
q^{(k-j)/2}\mathscr Y_j^C.
\]

Therefore
\[
\dim(\text{invisible})
=
\sum_{\substack{s<j\le k\\j\equiv k\ (2)}}(h_j-h_{j-2})
=h_k-h_s.
\]

For \(m\ge2\), this is precisely your proposed sum
\[
\sum_{\substack{m<j\le k\\j\equiv k\ (2)}}(h_j-h_{j-2}).
\]

The summands here are **harmonic angular sectors multiplied by powers of \(q\)**, not individual Hermite chaos spaces. Such a summand generally occupies several chaos degrees.

For even \(k\) and \(m=0\) or \(1\), your sum misses the one-dimensional radial sector \(q^{k/2}\): that sector is also invisible, so the kernel is all of \(\mathcal H_k\).

### Why the trace description works

For \(h_j\in\mathscr Y_j^C\),
\[
\Delta_C(q^a h_j)
=
2a(2j+d+2a-2)\,q^{a-1}h_j.
\]
Thus \(\Delta_C^{(k-s)/2}\) annihilates precisely the sectors with \(j>s\), and maps the remaining sectors isomorphically, up to nonzero scalar factors, onto the Fischer decomposition of \(\mathcal H_s\).

## 3. Orthogonality and integration-by-parts formulations

### The always-correct orthogonality statement

Let
\[
\mathcal P_{\le m}^{\,0}
=
\{P\in\mathcal P_{\le m}:\mathbb E_\gamma P=0\}.
\]
Then
\[
\boxed{
\ker(\text{observation map})
=
\mathcal H_k\cap
\left(\mathcal P_{\le m}^{\,0}\right)^{\perp_\gamma}.
}
\]
Equivalently,
\[
Q-\mathbb E_\gamma Q\perp_\gamma\mathcal P_{\le m}.
\]

Replacing \(\mathcal P_{\le m}^{\,0}\) by \(\mathcal P_{\le m}\) requires justification, since covariance does not test the mean.

For \(k>0\) and \(m\ge2\), your existing identity provides exactly that justification:
\[
\operatorname{Cov}_\gamma(q,Q)=k\,\mathbb E_\gamma Q.
\]
Since \(q\in\mathcal P_{\le2}\), invisibility forces \(\mathbb E Q=0\). Hence
\[
\boxed{
m\ge2,\ k>0
\quad\Longrightarrow\quad
\ker(\text{observation map})
=
\mathcal H_k\cap(\mathcal P_{\le m})^{\perp_\gamma}.
}
\]
This also holds for odd \(k\), for any \(m\), because the mean is automatically zero.

### Caution about the proposed gradient identity

In general,
\[
\operatorname{Cov}_\gamma(f,g)
\ne
\mathbb E_\gamma[\langle C\nabla f,\nabla g\rangle].
\]
For example, with a standard one-dimensional Gaussian and \(f=g=x^2\), the two sides are \(2\) and \(4\).

If \(f\) lies in chaos degree \(j>0\), the correct identity is
\[
\operatorname{Cov}_\gamma(f,Q)
=
\frac1j\,
\mathbb E_\gamma[\langle C\nabla f,\nabla Q\rangle].
\]

For the low-degree tests, useful exact identities are
\[
\operatorname{Cov}_\gamma(x,Q)=C\,\mathbb E_\gamma[\nabla Q],
\]
and
\[
\operatorname{Cov}_\gamma(xx^\top,Q)
=
C\,\mathbb E_\gamma[\nabla^2Q]\,C.
\]
These already settle the degree-\(\le2\) case without any Hermite infrastructure.

## 4. A minimal Hermite-free formalisation route

I would **not** start by formalising an orthogonal decomposition of all polynomial spaces. A finite differential transform plus a trace-surjectivity lemma is enough.

### A. Algebraic polynomial infrastructure

Use finite-dimensional spaces of homogeneous multivariate polynomials, with:

1. \(\Delta_C:\mathcal H_n\to\mathcal H_{n-2}\);
2. \(\dim\mathcal H_n=\binom{d+n-1}{n}\);
3. surjectivity of \(\Delta_C:\mathcal H_n\to\mathcal H_{n-2}\).

For item 3, a full Fischer decomposition is optional. The identity
\[
\Delta_C(qP)=(2d+4n)P+q\Delta_CP,
\qquad P\in\mathcal H_n,
\]
allows construction of a right inverse by a finite alternating sum involving
\[
qP,\ q^2\Delta_CP,\ q^3\Delta_C^2P,\ldots.
\]
All denominators are positive for \(d\ge1\).

This gives iterated-trace surjectivity and the kernel dimension directly by rank–nullity.

### B. A finite “centred test” transform

Define, on polynomials,
\[
\mathcal W_CA
=
\sum_{r\ge0}\frac{(-1)^r}{2^r r!}\Delta_C^rA,
\]
where the sum is finite by degree.

You need only:

- \(\mathcal W_CA\) has leading homogeneous term \(A\);
- the transformed homogeneous tests of degrees \(0,\ldots,m\) span \(\mathcal P_{\le m}\);
- if \(A\) is homogeneous of positive degree, \(\mathbb E[\mathcal W_CA]=0\).

This is Hermite machinery in substance, but requires **no multivariate Hermite basis or orthogonality library**.

### C. One Gaussian pairing lemma

For homogeneous \(A\in\mathcal H_j\), prove
\[
\mathbb E_\gamma[(\mathcal W_CA)Q]
=
\mathbb E_\gamma[A(C\partial)Q].
\]
This follows by repeated Gaussian integration by parts.

For \(Q\in\mathcal H_k\), it becomes
\[
\mathbb E_\gamma[(\mathcal W_CA)Q]
=
\frac{1}{2^r r!}
\left[A(C\partial)\Delta_C^rQ\right](0),
\qquad r=\frac{k-j}{2},
\]
with zero pairing for incompatible degrees/parities.

The bilinear form on \(\mathcal H_j\)
\[
(A,B)\longmapsto[A(C\partial)B](0)
\]
is nondegenerate. After whitening, it is simply
\[
\sum_{|\alpha|=j}\alpha!\,a_\alpha b_\alpha.
\]

These facts prove the kernel theorem immediately:

- tests of degree \(s\) detect exactly \(\Delta_C^{(k-s)/2}Q\);
- lower compatible tests detect further traces;
- opposite parity tests vanish.

The standard auxiliary moment lemma is
\[
\mathbb E_\gamma P
=
\left[e^{\Delta_C/2}P\right](0).
\]
You can prove it by polynomial Stein recursion; no analytic infinite series is involved.

**For the dimension theorem, nothing about a global orthogonal-complement basis is needed.** Fischer decomposition can be added later if you want the angular-sector interpretation.

### D. Explicit counterexamples: use harmonic polynomials, not univariate Hermites

A degree-\(k\) univariate Hermite polynomial is generally **not homogeneous**, so it is not a valid element of \(\mathcal H_k\).

Instead, whiten coordinates so that \(y\sim N(0,I)\). For \(d\ge2\), take
\[
Q_k(y)
=
\operatorname{Re}(y_1+i y_2)^k
=
\sum_{r=0}^{\lfloor k/2\rfloor}
(-1)^r\binom{k}{2r}y_1^{k-2r}y_2^{2r}.
\]
It is nonzero, homogeneous, and harmonic. Therefore it is orthogonal to every polynomial of degree less than \(k\).

For Lean, the real finite sum avoids complex numbers entirely. Once the pairing lemma above exists, certifying invisibility only requires checking \(\Delta Q_k=0\).

For the concrete low-order note, use
\[
y_1^3-3y_1y_2^2,\qquad
y_1^4-6y_1^2y_2^2+y_2^4.
\]

## 5. What degree-\(\le2\) monomials see

There are
\[
d+\frac{d(d+1)}2=\frac{d(d+3)}2
\]
nonconstant observables.

### Cubic jets

For \(Q_3\in\mathcal H_3\),
\[
\boxed{Q_3\text{ invisible}\iff\Delta_CQ_3=0.}
\]

Only the linear tests contribute. They recover the single trace \(\Delta_CQ_3\in\mathcal H_1\), since
\[
\operatorname{Cov}_\gamma(x,Q_3)
=
\frac12C\nabla(\Delta_CQ_3).
\]

Thus:

- visible dimension: \(d\);
- invisible dimension:
  \[
  \binom{d+2}{3}-d
  =\frac{d(d-1)(d+4)}6;
  \]
- invisible part: harmonic cubics;
- homogeneous visible complement: \(q\,\mathcal H_1\).

### Quartic jets

For \(Q_4\in\mathcal H_4\),
\[
\boxed{Q_4\text{ invisible}\iff\Delta_CQ_4=0.}
\]

Only the quadratic tests contribute. They recover the full quadratic trace \(\Delta_CQ_4\), because
\[
\operatorname{Cov}_\gamma(xx^\top,Q_4)
=
\frac12C\,\nabla^2(\Delta_CQ_4)\,C.
\]

Thus:

- visible dimension: \(\binom{d+1}{2}\);
- invisible dimension:
  \[
  \binom{d+3}{4}-\binom{d+1}{2}
  =\frac{d(d+1)(d-1)(d+6)}{24};
  \]
- invisible part: harmonic quartics;
- homogeneous visible complement:
  \[
  q\,\mathscr Y_2^C\oplus q^2\mathscr Y_0^C.
  \]

In particular, quadratic tests see the scalar radial quartic component as well as the traceless quadratic-trace component. They also determine \(\mathbb E Q_4\), through your identity \(\operatorname{Cov}(q,Q_4)=4\mathbb E Q_4\).

## 6. First invisible degree and observable budget

For \(d\ge2\):

- every positive degree \(k\le m\) is fully identified;
- the **first invisible positive degree is \(k=m+1\)**;
- nonzero invisible directions exist at every \(k>m\).

There is no parity delay to \(m+2\): harmonic polynomials give counterexamples already at \(m+1\). Parity changes the visible rank, not the first failure degree.

For \(d=1\), the situation differs: \(x\) and \(x^2\) already detect every positive-degree homogeneous polynomial. The theorem above captures this because \(h_k=1\) for every \(k\).

Finally, with the complete monomial design
\[
D=\binom{d+m}{m}
\]
including the useless constant observable, you identify every positive jet degree through \(m\), but not all degree-\((m+1)\) directions when \(d\ge2\).

For a budget \(N\) of **nonconstant monomial observables**, this design gives
\[
m=\max\left\{r:\binom{d+r}{r}-1\le N\right\},
\]
asymptotically \(m\sim(d!N)^{1/d}\) for fixed \(d\).

This is a statement about the **complete low-degree monomial design**, not an optimal lower bound for arbitrary observable families. For identifying a single \(\mathcal H_k\), the basic necessary count is only \(N\ge h_k\), consistent with your degree-\(k\) monomial injectivity result.