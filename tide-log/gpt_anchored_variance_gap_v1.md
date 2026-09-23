## 1. Correctness of A–D and cumulant consistency

**Yes, with the standing assumptions made explicit:** \(H\) and \(P\) are symmetric, \(P\succ0\), and for the bounds in C, \(\lambda_i>0\), \(g\ge0\), \(t\ge1\). The anchor parameters are fixed as \(t\) varies.

### A: general tilted variance

Write
\[
q(u)=u^\top Hu,\qquad b(u)=m^\top Hu,\qquad c=m^\top Hm,
\quad m=\Sigma v,\quad \Sigma=P^{-1}.
\]
Symmetry of \(H\) gives
\[
q(u+m)=q(u)+2b(u)+c,
\]
so the proposed square expansion is correct. Under the centred Gaussian,
\[
\mathbb E[q^2]=(\operatorname{tr}(H\Sigma))^2
                +2\operatorname{tr}(H\Sigma H\Sigma),
\qquad
\mathbb E[b^2]=(Hm)^\top\Sigma(Hm).
\]
The odd terms vanish, and subtracting
\((\operatorname{tr}(H\Sigma)+c)^2\) leaves exactly
\[
\operatorname{Var}_{P,v}(q)
=2\operatorname{tr}(H\Sigma H\Sigma)
 +4(Hm)^\top\Sigma(Hm).
\]
Thus the factor \(4\), and the stated formula for \(Q=q/2\), are correct.

### B: eigen-coordinate formula

This follows exactly:
\[
t^2\operatorname{Var}_{tH+gI,v}(Q)
=\frac12\sum_i\left(\frac{t\lambda_i}{t\lambda_i+g}\right)^2
 +t^2\sum_i\frac{\lambda_i^2a_i^2}{(t\lambda_i+g)^3}.
\]
Here \(a=U^\top v\). In D, ensure the bridge really identifies this \(a_i\) with \(g u_{0i}\): that requires \(u_0\) to denote the **E2-coordinate anchor**, rather than an unrotated ambient vector.

### C: correct, with a cleaner explicit remainder

Your central-term identity is exact. Setting \(u=t\lambda>0\),
\[
0\le
\frac12\left(\frac{u}{u+g}\right)^2-\frac12+\frac gu
=\frac{g^2}{u(u+g)}+\frac{g^2}{2(u+g)^2}
\le\frac{3g^2}{2u^2}.
\]

For the noncentral term, avoid the larger cubic numerator bound. Put \(r=u/(u+g)\in[0,1]\). Then
\[
0\le1-r^3=(1-r)(1+r+r^2)\le\frac{3g}{u}.
\]
Consequently,
\[
\left|
\frac{t^2\lambda^2a^2}{(t\lambda+g)^3}
-\frac{a^2}{\lambda t}
\right|
=\frac{a^2}{\lambda t}(1-r^3)
\le\frac{3ga^2}{\lambda^2t^2}.
\]
A convenient constant is therefore
\[
\boxed{K_{\rm anch}
=\sum_i\frac{\frac32g^2+3ga_i^2}{\lambda_i^2}.}
\]
These bounds actually hold for every \(t>0\). If \(g<0\) is permitted, positivity of denominators alone does not validate these particular bounds; use a sufficiently large threshold and different constants.

### D: correct coefficient and remainder

Define
\[
E_1^{\rm loc}=\sum_i e_{1i},
\qquad
E_1^{\rm anch}=\frac12\sum_i\frac{a_i^2-g}{\lambda_i}.
\]
Then
\[
C_1'=E_1^{\rm loc}-E_1^{\rm anch},
\]
and the variance correction difference is \(2C_1'\). In inequality form,
\[
\left|
t^2\operatorname{Var}_{\rm loc}(L\circ A)
-t^2\operatorname{Var}_{\rm anch}(Q)
-\frac{2C_1'}t
\right|
\le\frac{K_{\rm loc}+K_{\rm anch}}{t^2}
\]
on the common validity range.

### Cumulant check

For \(X_t=tL\), the proposed transform expansion gives, algebraically,
\[
\log\Lambda_t(s)
=-\frac d2\log(1+s)-\frac{E_1}{t}\frac{s}{1+s}
+O(t^{-2}).
\]
Since
\[
\frac{s}{1+s}=s-s^2+s^3-\cdots,
\]
and \(\log\mathbb E[e^{-sX_t}]\) has first derivative \(-\mathbb E[X_t]\) and second derivative \(\operatorname{Var}(X_t)\) at zero, the corrections are indeed
\[
\mathbb E[X_t]=\frac d2+\frac{E_1}{t}+O(t^{-2}),
\qquad
\operatorname{Var}(X_t)=\frac d2+\frac{2E_1}{t}+O(t^{-2}).
\]

**Important logical qualification:** this is a consistency check, not permission to differentiate a pointwise \(O(t^{-2})\) remainder. Deriving the moment theorems from the transform theorem requires derivative control near \(s=0\), or suitable analytic-uniform estimates. Your separately landed moment estimates avoid that issue.

## 2. Odd moments and Wick bookkeeping in Lean

### Odd moments: prefer the existing Stein infrastructure

I would add a reusable coordinate lemma
\[
\int u_j u_a u_b\,gw=0
\]
using `gaussian_stein_prod_coord_matCLM` with `n = 2`, followed by the first-moment-zero lemma:
\[
\int u_j u_a u_b\,gw
=\Sigma_{ja}\int u_b\,gw+\Sigma_{jb}\int u_a\,gw=0.
\]
This works with repeated indices too; no distinctness hypotheses belong in the statement.

Then expand the scalar linear and quadratic forms into finite sums and apply the first- and third-moment lemmas termwise. Use `integrable_prod_coord_mul_gaussianWeight_matCLM` to justify distributing the integral over the sums; multiplication by fixed coefficients preserves integrability.

A reflection proof is mathematically shorter at the polynomial level:
\[
gw(-u)=gw(u),\qquad F(-u)=-F(u)
\quad\Longrightarrow\quad \int F\,gw=0.
\]
But with only the stated matrix change-of-variables lemma, it adds determinant and `mulVec` normalization work for \(-I\). **Use Stein now; use reflection if you already have, or want independently, a general odd-function Gaussian integral lemma.**

### Wick contractions: split them before doing trace algebra

Write
\[
T=\operatorname{tr}(H\Sigma),\qquad
S=\operatorname{tr}(H\Sigma H\Sigma).
\]
After Wick, the three coefficient sums are:

1. **Disconnected contraction**
   \[
   \sum_{a,b,c,d}H_{ab}H_{cd}\Sigma_{ab}\Sigma_{cd}=T^2.
   \]
   Here \(\Sigma_{ab}=\Sigma_{ba}\) identifies
   \(\sum_{a,b}H_{ab}\Sigma_{ab}\) with the trace.

2. **First connected contraction**
   \[
   \sum_{a,b,c,d}H_{ab}H_{cd}\Sigma_{ad}\Sigma_{bc}=S.
   \]
   Indeed,
   \[
   S=\sum_{a,c,b,d}H_{ab}\Sigma_{bc}H_{cd}\Sigma_{da},
   \]
   so this is your proposed order, using symmetry of \(\Sigma\).

3. **Second connected contraction**
   \[
   \sum_{a,b,c,d}H_{ab}H_{cd}\Sigma_{bd}\Sigma_{ac}=S.
   \]
   Swap \(c,d\), use \(H_{dc}=H_{cd}\), and it becomes the first connected contraction.

In Lean, prove these as separate finite-sum identities. Use `Finset.sum_comm` for binder permutations and `ring` only once the binders are aligned. A giant `simp`/`ring` over the whole fourth-moment calculation is likely to be brittle: scalar commutativity does not reorder nested summation binders.

Also establish the nonzero/positive Gaussian normalization before quotient cancellation.

## 3. Nearby stronger target

The useful extension is exactly
\[
\boxed{
\operatorname{Cov}_{P,v}(u^\top Hu,u^\top Ku)
=2\operatorname{tr}(H\Sigma K\Sigma)
 +4(Hm)^\top\Sigma(Km)
}
\]
for symmetric \(H,K\). For half-quadratic probes, this becomes
\[
\operatorname{Cov}_{P,v}\!\left(\tfrac12u^\top Hu,\tfrac12u^\top Ku\right)
=\tfrac12\operatorname{tr}(H\Sigma K\Sigma)
 +(Hm)^\top\Sigma(Km).
\]
No commutation of \(H,K,\Sigma\) is required.

I would **not make this a dependency of D**. Once A is proved, polarization gives the mixed identity from the variances for \(H+K,H,K\). It needs covariance algebra, integrability, and trace cyclicity, but no new fourth-moment analysis.

If your covariance bilinearity infrastructure is already convenient, fold it in as a corollary. Otherwise A is already the full general-tilt second-cumulant identity needed this tide; defer the mixed version rather than delaying the anchored gap.

## 4. Wording against E3

The wording is fair with “leading discrepancies” or “admit the expansions” replacing an unconditional “differ at order \(1/t\).” Suggested version:

> For fixed admissible parameters and anchor, the exact localised law and the anchored Gaussian prediction have scaled-energy mean, variance, and Laplace-transform discrepancies
> \[
> \frac{C_1'}t+O(t^{-2}),\qquad
> \frac{2C_1'}t+O(t^{-2}),\qquad
> -\frac{sC_1'}{(1+s)^{d/2+1}t}+O(t^{-2}),
> \]
> respectively, with discrepancies taken as exact minus Gaussian. Thus a single coefficient \(C_1'\) controls all three leading corrections.

Qualifications:

- These are the mean and variance of the **scaled energies** \(t(L\circ A)\) and \(tQ\).
- If \(C_1'=0\), the discrepancies are \(O(t^{-2})\), not necessarily genuinely order \(1/t\). At \(s=0\), the transform discrepancy is exactly zero.
- State the landed admissible range of \(s\). Do not claim uniformity in \(s\), dimension, or parameters beyond the proved bounds; in particular, behavior near \(s=-1\) needs separate care.
- \(C_1'\) includes the anchor–cubic interaction, not merely the unanchored anharmonic coefficient.
- These are three observable-level asymptotics, not by themselves a distributional-distance estimate or a universal ranking of sampling schemes.

## 5. Recommended scope

Land A as reusable Gaussian infrastructure, B as its localised spectral specialization, C with the explicit bound above, and D as the main comparison theorem. Keep coordinate third moments and Wick contraction identities as small supporting lemmas. Treat mixed quadratic covariance as an optional polarization corollary.

**Vote: formalise A → B → C → D this tide; add mixed covariance only if the existing covariance algebra makes it genuinely cheap.**