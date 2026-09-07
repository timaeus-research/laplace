Querying gpt-6-astra (timeout: 540s)...
Response received in 152.5s
The main new conclusion is that **the grouped density coefficients are simpler than the over-complete statement suggests**: the constant coefficient is the sum of the two face finite parts, and the logarithmic coefficient is the compatible corner jet at a collision. There is no additional corner correction to the grouped constant.

I would next prioritize grouping, envelope-to-moment discharge, and a genuine smooth rectangular-remainder lemma. A bivariate formal-power-series development is not necessary for the smooth specialization.

## (a) Grouping and cancellations

Write
\[
q_i=\frac{i}{k_1},\qquad t_j=\frac{j}{k_2},\qquad
\tau_0=\min\left(\frac{M_1}{k_1},\frac{M_2}{k_2}\right),
\]
and assume \(b>0\).

### Exact nonresonant cancellations

For \(q_i\ne t_j\), put
\[
d_{ij}=k_1(t_j-q_i)=\frac{k_1j}{k_2}-i.
\]
The \(u\)-face monomial coefficient at exponent \(p+t_j\) is
\[
-\frac{1}{k_1}
 \frac{b^{-(k_1/k_2)(j-k_2i/k_1)}}{j-k_2i/k_1}\,c_{ij}
=
-\frac{b^{-d_{ij}}}{k_2d_{ij}}c_{ij}.
\]
This is exactly the corner finite-part coefficient
\[
\frac{c_{ij}}{k_2}\operatorname{axisPrim}(d_{ij},b,0).
\]
The corresponding \(v\)-face monomial coefficient equals the corner monomial coefficient at \(p+q_i\). Thus subtracting the corner removes both nonresonant monomial contributions.

### Resonance

At \(q_i=t_j\), the logarithmic density coefficients combine as
\[
\frac{c_{ij}}{k_1k_2}
+\frac{c_{ij}}{k_1k_2}
-\frac{c_{ij}}{k_1k_2}
=\frac{c_{ij}}{k_1k_2}.
\]

The *additional* constant contributions outside the two face finite parts are
\[
\frac{c_{ij}\log b}{k_2}
+\frac{c_{ij}\log b}{k_1}
-\left(
 \frac{c_{ij}\log b}{k_1}
 +\frac{c_{ij}\log b}{k_2}
\right)=0.
\]
Consequently the net constant density coefficient at this collision is
\[
\boxed{
\frac1{k_1}\operatorname{FP}_{k_2q_i}(a_i)
+\frac1{k_2}\operatorname{FP}_{k_1q_i}(b_j).
}
\]

This does **not** say that the collision contributes no endpoint constant: those constants are already inside the face finite parts. For the single monomial \(c_{ij}u^iv^j\), the displayed expression becomes
\[
c_{ij}\left(\frac1{k_1}+\frac1{k_2}\right)\log b,
\]
as it should.

### Canonical grouped statement

For any \(0<\tau\le\tau_0\), let
\[
Q_\tau=
\{q_i:i<M_1,\ q_i<\tau\}
\cup
\{t_j:j<M_2,\ t_j<\tau\}.
\]
Define the density coefficients
\[
\begin{aligned}
D_q(s)
&=
\frac1{k_1}
 \sum_{\substack{i<M_1\\q_i=q}}
 \operatorname{FP}_{k_2q}(a_i(\cdot,s))
+
\frac1{k_2}
 \sum_{\substack{j<M_2\\t_j=q}}
 \operatorname{FP}_{k_1q}(b_j(\cdot,s)),\\
L_q(s)
&=
\frac1{k_1k_2}
 \sum_{\substack{i<M_1,\ j<M_2\\q_i=t_j=q}}c_{ij}(s).
\end{aligned}
\]
Each single-index sum has at most one term; the double sum also has at most one term.

To state the transferred coefficients without depending on your kernel normalization, write
\[
\mathcal M_\alpha[F]
=\int_0^\infty s^{\alpha-1}W(s)F(s)\,ds
\]
for the moment functional used by `face_transfer_bound`. Then
\[
\boxed{
A_q=\mathcal M_{p+q}[L_q],\qquad
B_q=\mathcal M_{p+q}[D_q]
      -\mathcal M_{p+q}[L_q\log s].
}
\]
Thus
\[
Z_\Phi(N)=
\sum_{q\in Q_\tau}
N^{-(p+q)}(A_q\log N+B_q)
+
O\!\left(N^{-(p+\tau)}(1+\log N)\right).
\]
These formulas use scaling \(s=Nr\). If the paper uses \(N=\sqrt n\), the coefficient of \(\log n\) is \(A_q/2\).

Terms at \(q=\tau\) should be omitted and absorbed into the stated remainder. The convenient cutoff choice
\[
M_\ell=\lceil k_\ell\tau\rceil
\]
automatically gives your two strict truncation inequalities.

### Lean route

**Regroup the theorem you already have.** I would not reconstruct the analytic proof using reduced faces.

1. Prove the two nonresonant coefficient equalities.
2. Prove the resonant logarithmic and constant identities.
3. Establish a finite-sum identity, with no integration or asymptotics.
4. Apply linearity of the already justified moment integrals.
5. Absorb the finite collection of terms with \(q\ge\tau\).

For indexing, use rational shifts when the \(k_\ell\) are natural numbers; otherwise use the finite image of your existing real-valued exponent map. Avoid introducing a quotient unless needed.

The reduced decomposition is useful as an explanatory lemma, but its finite parts require linearity and endpoint bookkeeping that reproduce the same algebra. The **grouped finite-part formula** is closest to a Taylor-tree coefficient description; identifying the actual paper tree indices remains a separate task.

## (b) Smooth specialization

There is a third route, cheaper than either proposed alternative:

> **Iterate one-dimensional Taylor remainder bounds using commuting coordinate Taylor operators.**

### Sufficient hypotheses

A clean paper-facing assumption is:

- \(\xi,\eta\) are \(C^K\) on an open neighborhood of \([0,b]^2\);
- \(K\ge M_1+M_2\);
- \(s\ge0\), \(\beta\ge0\);
- \(\xi\le L\) on the box.

Compactness then supplies bounds on all required derivatives. For Lean, an initial theorem with **explicit bounds on rectangular mixed derivatives** is easier than immediately extracting every bound from `ContDiffOn` and compactness.

The exponential product satisfies, for \(a\le M_1,\ b'\le M_2\),
\[
\sup_{(u,v)\in[0,b]^2}
|\partial_u^a\partial_v^{b'}\Phi(u,v,s)|
\le C_{a,b'}(1+s)^{a+b'}e^{\beta sL}.
\]
This follows by repeated product and chain rules. You need only a bound, not an explicit bivariate Bell-polynomial formula.

Set
\[
a_i(v,s)=\frac{\partial_u^i\Phi(0,v,s)}{i!},
\quad
b_j(u,s)=\frac{\partial_v^j\Phi(u,0,s)}{j!},
\quad
c_{ij}(s)=\frac{\partial_u^i\partial_v^j\Phi(0,0,s)}{i!j!}.
\]
Mixed-partial commutation gives compatibility.

### Remainders

The ordinary Taylor bound gives
\[
\left|a_i(v,s)-\sum_{j<M_2}c_{ij}(s)v^j\right|
\le
\frac{C_{i,M_2}}{i!M_2!}
(1+s)^{i+M_2}e^{\beta sL}v^{M_2},
\]
and symmetrically for \(b_j\).

Let \(P_u,P_v\) be the two Taylor projections and \(Q_u=I-P_u,\ Q_v=I-P_v\). Then
\[
R=Q_uQ_v\Phi
\]
and
\[
|R(u,v,s)|
\le
\frac{C_{M_1,M_2}}{M_1!M_2!}
u^{M_1}v^{M_2}(1+s)^{M_1+M_2}e^{\beta sL}.
\]

A particularly economical proof applies the \(u\)-Taylor bound to \(Q_v\Phi\), then bounds
\[
\partial_u^{M_1}Q_v\Phi
=Q_v(\partial_u^{M_1}\Phi)
\]
using the \(v\)-Taylor bound. No multivariate Taylor theorem or double integral remainder is required.

### Recommendation

- First: rectangular Taylor with abstract mixed-derivative bounds.
- Second: specialize the derivative bounds to \(\eta e^{\beta s\xi}\).
- Later: derive explicit jet formulas if the paper needs them.

Analytic double series give a useful stronger-hypothesis corollary, but they do not establish the advertised smooth theorem. `MvPolynomial` is appropriate for explicit jet identities, not the shortest route to these estimates.

## (c) Moment hypotheses from envelopes

Your proposed finite-part estimate is exactly right:
\[
\boxed{
|\operatorname{FP}_\gamma(\Psi(\cdot,s))|
\le
\frac{b^{M-\gamma}}{M-\gamma}H(s)
+
\sum_{m<M}|f_m(s)|
\,|\operatorname{axisPrim}(\gamma,b,m)|.
}
\]
Here \(M>\gamma\), and the proof is simply the integral triangle inequality followed by
\[
\int_0^b v^{M-\gamma-1}\,dv
=\frac{b^{M-\gamma}}{M-\gamma}.
\]

If all \(H,f_m\) have envelopes
\[
C_\ell(1+s)^{D_\ell}e^{\beta a'_\ell s},
\]
take maxima of the finitely many \(D_\ell,a'_\ell\) and sum the scaled constants. This gives the same envelope form for every face coefficient, including the finite part.

The numerical restriction on \(a'\) depends on the weight in your existing moment lemma:

- For a weight \(e^{-\beta a s}\), require \(a'<a\).
- For a Gaussian weight \(e^{-\beta a s^2}\), with \(\beta a>0\), every finite \(a'\) is allowed.
- More generally, use exactly the decay margin in `moment_integrableOn_of_envelope`.

The identifier alone does not determine which restriction applies.

The important endpoint conditions are:

1. For a moment with power \(s^{\alpha-1}\), require \(\alpha>0\).
2. The factor \(1+|\log s|\) is harmless at zero under the same condition:
   \[
   \int_0^1s^{\alpha-1}|\log s|\,ds<\infty.
   \]
   It does not rescue \(\alpha=0\).
3. At infinity, logarithmic weights cost only a polynomial factor.
4. For shifted remainder moments, check the shifted exponent separately.
5. Include measurability of the finite-part map in \(s\). A pointwise bound does not establish it; obtain it from measurable parameter integration of the subtracted integrand.

A useful packaging is an envelope lemma for `FP`, followed by one constructor proving the entire `FaceMoments` bundle.

## (d) Explicit constant-kernel bounds

**Invest in the explicit product-density bound.** But it only makes the mixed-remainder step quantitative; it does not by itself make every use of `IsBigO` in the face transfer quantitative.

Here is a normalization-independent theorem that can feed all the variants. Let
\[
J(\lambda)=
\int_0^b\int_0^b
u^{h_1}v^{h_2}g(\lambda u^{k_1}v^{k_2})\,dv\,du,
\]
where \(g\ge0\), \(k_i>0\), \(h_i>-1\), and
\[
p_i=\frac{h_i+1}{k_i},\qquad R=b^{k_1+k_2}.
\]
Put
\[
M_\alpha=\int_0^\infty s^{\alpha-1}g(s)\,ds,\qquad
U_{\alpha,R}=
\int_0^\infty s^{\alpha-1}g(s)\log_+(R/s)\,ds.
\]

### Equal exponents

For \(p_1=p_2=p\),
\[
\rho(r)=\frac{r^{p-1}}{k_1k_2}\log(R/r),
\qquad 0<r<R.
\]
For every \(\lambda\ge1\),
\[
\boxed{
J(\lambda)\le
\frac{\lambda^{-p}}{k_1k_2}
\bigl(M_p\log\lambda+U_{p,R}\bigr).
}
\]
This follows directly from
\[
\log(\lambda R/s)\le\log\lambda+\log_+(R/s).
\]

For \(\lambda=\sqrt n\), \(n\ge1\),
\[
J(\sqrt n)\le K n^{-p/2}(1+\log n),
\quad
K=\frac1{k_1k_2}\max\{M_p/2,U_{p,R}\}.
\]

### Unequal exponents

Suppose \(p_1<p_2\), \(\delta=p_2-p_1\). Then
\[
\rho(r)=
\frac{b^{k_2\delta}}{k_1k_2\delta}
r^{p_1-1}\left[1-(r/R)^\delta\right].
\]
Hence
\[
\boxed{
J(\lambda)\le
\frac{b^{k_2\delta}}{k_1k_2\delta}
M_{p_1}\lambda^{-p_1}.
}
\]
The symmetric formula applies when \(p_2<p_1\).

Also prove the gap-uniform alternative
\[
\boxed{
J(\lambda)\le
\frac{b^{k_2\delta}}{k_1k_2}
\lambda^{-p_1}
\bigl(M_{p_1}\log\lambda+U_{p_1,R}\bigr),
}
\]
using \((1-x^\delta)/\delta\le\log(1/x)\). **This second estimate is important for parameter integration near a collision:** the first has an artificial \(1/\delta\) blow-up.

For your mixed remainder, use the shifted \(h_i+M_i\) and put the \(s\)-envelope into \(g\).

If \(g\) is bounded, a small-\(\lambda\) bound is
\[
J(\lambda)\le
\|g\|_\infty
\frac{b^{h_1+1}}{h_1+1}
\frac{b^{h_2+1}}{h_2+1}.
\]
For example, if the actual dominating kernel is
\(e^{-\beta a s^2+\beta Ls}\), then its supremum is at most
\(e^{\beta L_+^2/(4a)}\).

Finally, construct \(K(w)\) from these bounds **and the explicit face-transfer constants**. Pointwise `IsBigO` or compactness in \(n\) does not give an integrable parameter envelope for \(K(w)\). Check the wrapper’s strict gap after converting between \(N\) and \(n\).

## (e) General \(d\)

The honest recursive structure is the calculus of **commuting coordinate Taylor projections and weighted finite parts**.

For coordinate projections \(P_\ell\) and \(Q_\ell=I-P_\ell\),
\[
\Phi=
\sum_{\varnothing\ne S\subseteq\mathrm{Fin}\,d}
(-1)^{|S|+1}
\left(\prod_{\ell\in S}P_\ell\right)\Phi
+
\left(\prod_{\ell=1}^dQ_\ell\right)\Phi.
\]
The final term has a product remainder
\[
|R(x,s)|\le H(s)\prod_\ell x_\ell^{M_\ell}.
\]
Every other term is polynomial in at least one coordinate, permitting recursive density/finite-part reduction.

Two cautions:

- Lower-dimensional coefficients are generally **renormalized face integrals**, with overlapping subface counterterms—not merely ordinary integrals over faces.
- Independence of the order of iterated finite parts needs a theorem under the rectangular subtraction and integrability hypotheses.

For the equal-exponent constant block,
\[
\rho_d(r)=
\frac{r^{p-1}}{(d-1)!\prod_\ell k_\ell}
\left(\log(R/r)\right)^{d-1},
\qquad R=b^{\sum_\ell k_\ell}.
\]
This is an excellent first analytic general-\(d\) result.

At a candidate exponent \(\alpha\), the maximal log degree is one less than its multiplicity among the coordinate Taylor spectra
\[
\left\{\frac{h_\ell+j+1}{k_\ell}:j\ge0\right\}.
\]
Coefficients may vanish, so this is an upper bound, not an assertion that the top log is present.

**First algebraic unit:** abstract finite-set inclusion–exclusion for commuting Taylor operators.  
**First analytic unit:** equal-exponent constant product density and its explicit bound.  
Then use \(d=3\) to test the finite-part coefficient calculus before claiming an all-order arbitrary-\(d\) theorem.

## (f) Paper-facing annotations

### `thm:TaylorTree`

The formal development proves all-order one-dimensional expansions with explicit coefficients and identifies their Taylor data canonically with derivatives. It also proves two-dimensional equal-exponent block expansions to arbitrary finite cutoff order, with logarithmic terms arising at exponent collisions and coefficients expressed through weighted axis finite parts. The current checked two-dimensional theorem uses an over-complete face–corner listing; the grouped coefficient formula above still requires a finite algebraic regrouping theorem. The analytic moment hypotheses remain explicit assumptions, and neither arbitrary-dimensional Taylor trees nor the paper’s tree indexing has yet been identified.

### `cor:standardintegralexp`

The one-dimensional smooth standard-integral expansion is formalized to all orders, including canonical derivative identification and truncation independence. In two dimensions, a finite-cutoff expansion is available under compatible face Taylor data, mixed-remainder bounds, and bundled moment assumptions. Convergent axis-series formulas identify the established two-dimensional constant coefficients. A theorem deriving all two-dimensional hypotheses directly from smooth \(\eta,\xi\), and an instantiation for mixed critical/noncritical blocks, remain to be supplied.

### `eq:flucttreeterms`

The development establishes the local coefficient calculus underlying one-dimensional fluctuation terms and two-dimensional equal-exponent blocks, including resonant logarithms and weighted finite-part constants. A strict-gap parameter-integration theorem transports suitable pointwise expansions under explicit weighted integrability and remainder hypotheses. The mixed-block application has not yet been instantiated with parameter-dependent quantitative envelopes. Accordingly, the full fluctuation-tree formula and its combinatorial indexing are not yet claimed as formalized.

## (g) Next five units, ranked

These are deliberately smaller than a complete smooth or mixed-block bridge.

### 1. Grouped two-dimensional cutoff theorem

**Statement:** under `twoD_cutoff_isBigO` hypotheses and \(0<\tau\le\tau_0\), prove the grouped \(Q_\tau,A_q,B_q\) expansion above.

**Scope:** coefficient cancellation lemmas, finite regrouping, and absorption of terms beyond cutoff.  
**Value:** immediately turns the existing analytic result into a paper-readable coefficient theorem.

### 2. Finite-part envelope and `FaceMoments` constructor

**Statement:** measurable Taylor data with \(M>\gamma\) satisfy the displayed finite-part bound; common admissible polynomial-exponential envelopes imply `FaceMoments`.

**Scope:** include parameter measurability, not just the norm estimate.  
**Value:** removes a large bundle of opaque assumptions from applications.

### 3. Rectangular smooth Taylor remainder

**Statement:** explicit bounds on mixed derivatives through \((M_1,M_2)\) imply compatible face jets, face remainder bounds, and
\[
|Q_uQ_vF|\le
\frac{u^{M_1}v^{M_2}}{M_1!M_2!}
\sup|\partial_u^{M_1}\partial_v^{M_2}F|.
\]

**Scope:** abstract \(F\); do not include the full exponential specialization in this unit.  
**Value:** the central missing smooth bridge, using existing one-dimensional Taylor infrastructure.

### 4. Quantitative product-kernel majorant

**Statement:** prove the equal, unequal, and gap-uniform bounds for \(J(\lambda)\), plus the bounded-kernel small-\(\lambda\) estimate.

**Scope:** generic nonnegative \(g\) and its moments; specialize later.  
**Value:** replaces the mixed-remainder `IsBigO` bottleneck and avoids nonintegrable artificial gap constants.

### 5. Smooth exponential derivative envelope

**Statement:** bounded derivatives of \(\eta,\xi\) through the required rectangular orders, together with \(\xi\le L\), imply
\[
|\partial_u^a\partial_v^b(\eta e^{\beta s\xi})|
\le C_{a,b}(1+s)^{a+b}e^{\beta sL}.
\]
Apply unit 3 and unit 2 to obtain the smooth two-dimensional cutoff theorem under the appropriate kernel decay condition.

**Scope:** use derivative-bound induction rather than explicit bivariate jet polynomials; split off the final assembly if necessary.  
**Value:** closes the strongest remaining paper-facing specialization gap.

I would place general-\(d\) inclusion–exclusion immediately after these five. It is inexpensive algebra, but closing the grouped smooth \(d=2\) theorem first yields substantially more mathematical coverage per unit of formalization.
