## 1. Correctness

**(a) Yes**, assuming symmetric Taylor tensors \(T,Q\), and a symmetric positive-definite \(H\) for the probabilistic interpretation. Explicitly,
\[
\begin{aligned}
(Q:S)_{ij}&=\sum_{kl}Q_{ijkl}S_{kl},\\
\operatorname{bubble}_{ij}&=\sum_{klmn}T_{ikl}S_{km}S_{ln}T_{jmn},\\
\operatorname{tadpoleLine}_{ij}&=\sum_{klmn}T_{ijk}S_{kl}T_{lmn}S_{mn}.
\end{aligned}
\]
Then
\[
\Pi=-\frac t2(Q:S)+\frac{t^2}2\operatorname{bubble}
+\frac{t^2}2\operatorname{tadpoleLine},\qquad
\operatorname{Cov}_{\text{one-loop}}=S+S\Pi S.
\]
Signs and factors are correct: one quartic vertex contributes \(-t\); two cubic vertices contribute \(t^2\). The tadpole-line term remains in the **connected covariance** after subtracting the mean product. This is generally a perturbative prediction, not an exact covariance identity.

**(b) Your Rosenbrock arithmetic is correct.** In particular,
\[
\operatorname{tadpoleLine}
=\frac1{t^2}\begin{pmatrix}4a&0\\0&0\end{pmatrix}.
\]
Consequently, the quartic, bubble, and tadpole-line contributions to \(\Pi_{11}\) are respectively
\[
-6a,\qquad 8a^2+4a,\qquad 2a,
\]
leaving \(8a^2\). Thus
\[
\Pi=2a^2\begin{pmatrix}4&-2\\-2&1\end{pmatrix},
\qquad
S\Pi S=\frac2{t^2}\begin{pmatrix}0&0\\0&1\end{pmatrix}.
\]

**(c) Correct.** Setting \(x=u/\sqrt{\lambda t}\) gives
\[
tL(x)=u^2/2+\frac{\alpha}{6\lambda^{3/2}}\frac{u^3}{\sqrt t}
+\frac{\gamma}{24\lambda^2}\frac{u^4}{t}.
\]
Hence
\[
\frac{45A^2-12B}{\lambda}
=\frac{5\alpha^2}{4\lambda^4}-\frac{\gamma}{2\lambda^3},
\]
and subtracting \(\alpha^2/(4\lambda^4)\) gives your variance coefficient. The actual seabed definitions and mean-limit statement still need inspection; neither is supplied here in full.

## 2. Lean route

**(a)** Direct expansion is plausible, but **prove \(\Pi\) separately**. Better still, expose the three contraction evaluations as small lemmas. This avoids repeated four-fold expansions inside matrix multiplication and makes failures local.

Use explicit nonzero hypotheses:
```lean
have ha0 : a ≠ 0 := ne_of_gt ha
have ht0 : t ≠ 0 := ne_of_gt ht
```
Then `field_simp [ha0, ht0] <;> ring`. Prove the scaled inverse once and reuse it.

**(b)** Prefer **nested vectors** here. Both approaches reduce after all indices become numerals, but vectors avoid conditional/propositional normalization. For `rosenQ`, a simple “all indices zero” conditional is also perfectly reasonable. Expand sums and simplify zeros **before** invoking `ring`.

**(c)** First derive the eventual bound
```lean
hb : ∀ᶠ t in atTop,
  |t * (t * m₂ t - 1 / λ) - c₂ / λ| ≤ K / Real.sqrt t
```
by restricting to `t ≥ T`, hence `0 < t`, multiplying the given inequality by `t`, and using
\[
t(t m_2-1/\lambda)-c_2/\lambda
=t(t m_2-1/\lambda-c_2/(\lambda t)).
\]
Use `mul_le_mul_of_nonneg_left`, `abs_mul`, and `field_simp [ht.ne']`.

The limit idiom is then:
```lean
have hi : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
have hk : Tendsto (fun t : ℝ => K / Real.sqrt t) atTop (nhds 0) := by
  simpa [div_eq_mul_inv] using hi.const_mul K
have hz := squeeze_zero'
  (Filter.Eventually.of_forall (fun t : ℝ =>
    abs_nonneg (t * (t * m₂ t - 1 / λ) - c₂ / λ))) hb hk
have hsecond : Tendsto (fun t => t * (t * m₂ t - 1 / λ))
    atTop (nhds (c₂ / λ)) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)
```
This is the intended Mathlib idiom; I have not checked it against your pin.

Then:
```lean
have hvar := hsecond.sub (hmean.pow 2)
```
Its function is
```lean
fun t => t * (t * m₂ t - 1 / λ) - (t * m₁ t) ^ 2
```
Convert eventually to
```lean
fun t => t ^ 2 * ((m₂ t - (m₁ t) ^ 2) - 1 / (λ * t))
```
using `.congr'`, eventual `0 < t`, and `field_simp; ring`. Finally simplify the limiting coefficient. No quantitative mean remainder is needed.

## 3. Stronger nearby statement

**Quadratic curved valleys are a genuine generalization.** For
\[
g(x)=b x^2+c x+d,\qquad p=g'(\mu)=2b\mu+c,
\]
the exact covariance is
\[
\begin{pmatrix}
1/t&p/t\\
p/t&p^2/t+1/(at)+2b^2/t^2
\end{pmatrix}.
\]
The one-loop correction is exactly \(2b^2t^{-2}e_y e_y^\top\). This follows from the same shear-moment machinery and is a sensible follow-up, though not necessary for this tide.

**Do not generalize exactness merely from quartic Taylor termination:** generic quartic potentials have infinitely many nonzero asymptotic corrections.

Rosenbrock’s second-order LLC correction already vanishes by the supplied exact theorem `gibbsExpectation_rosenbrock_self`; an explicit corollary is cheap but adds little.

**Vote: A, with staged contraction lemmas; quadratic-valley exactness only as an optional extension.**