## Verdicts

| Unit | Verdict | Summary |
|---|---|---|
| **221 — `NormalCrossingPrior`** | **Faithful, with documentation caveats** | The hypotheses give finite, strictly positive evidence and a genuine normalized posterior density. The displayed theorem proves normalization of the quotient, not construction of a probability-measure object. |
| **222 — `MellinCoefficient`** | **Faithful with caveats** | The real-axis limit, constants, exponent convention, and regular-point generalization are correct. Wording should distinguish this limit from an actual Laurent expansion or an exact-order pole for arbitrary continuous amplitudes. |

This is a source-level statement and mathematical review; I have not run Lean or independently checked the imported files.

## Unit 221

### Hypotheses and positive evidence

The hypothesis
```lean
∀ x ∈ symBox 2, 0 ≤ ρ x
```
is appropriate. No nonnegativity outside the integration domain is needed. Pointwise nonnegativity is stronger than almost-everywhere nonnegativity, but is natural here.

`Continuous ρ` on all of `ℝ²` is an acceptable sufficient formulation of “extends continuously to the closed box.” It is formally stronger for an already specified ambient function, but does not materially restrict the admissible weights on the box: a continuous function on `[-1,1]²` can be extended globally by composing with coordinatewise clamping.

The mathematical mechanism is sound:

- continuity and `ρ(0)>0` give a positive lower bound on a small ball about the origin;
- that ball lies inside `symBox 2` and has positive volume;
- the kernel has a strictly positive lower bound there;
- the integrand is nonnegative elsewhere;
- continuity on the compact closed box gives integrability.

The likelihood factorization then gives finite positive evidence for every `n≥1` and every data vector `y`. No prior normalization is necessary: a finite nonzero prior weight can be normalized, and its normalization cancels from the posterior quotient.

### Calling the quotient a posterior expectation

Under these hypotheses there is mathematically a probability measure
\[
P_{n,y,\rho}(dx)
=\frac{\rho(x)\,\mathrm{ncLikelihood}(n,y,x)}{Z_{n,y,\rho}}\,
  (\mathrm{volume}\!\restriction\mathrm{symBox}\,2)(dx).
\]

Thus `ncPosteriorMean` is its posterior expectation **for posterior-integrable observables**.

One qualification matters: **boundedness alone does not imply integrability without measurability**. Bounded measurable observables on the box suffice; continuous-on-the-closed-box observables certainly suffice. If all observables used are continuous, there is no substantive gap.

`ncPosteriorMean_one` proves the expected normalization identity. Its docstring should not suggest that the theorem itself constructs a measure or proves an `IsProbabilityMeasure` instance.

## Unit 222

### 1. Transform convention and Laurent normalization

There is **no factor-2, sign, or `p/2` mismatch**. On the positive unit box,
\[
(u^{2k})^z u^h=\prod_i u_i^{2k_i z+h_i}.
\]
Putting \(z=-l+s\) gives exactly the Lean exponent.

Write
\[
A_i=h_i+1-2k_i l.
\]
For `η=1`,
\[
V(-l+s)=\prod_i\frac1{A_i+2k_i s}.
\]
For \(i\in J\), \(A_i=0\), so each minimizing coordinate contributes
\[
\frac1{2k_i s}.
\]
Consequently,
\[
s^mV(-l+s)\longrightarrow
\prod_{i\in J}\frac1{2k_i}
\prod_{i\notin J}\frac1{h_i+1-2k_i l}.
\]
This is precisely the paper’s \(a_{-m}\) at \(b=1\), with \(\gamma\) absorbed into \(h\).

If a meromorphic function has a pole of order \(m\) at \(-\lambda\), then
\[
s^mV(-\lambda+s)\to a_{-m}
\]
is the correct real-axis consequence of its Laurent expansion, with coefficient of \((z+\lambda)^{-m}\). **The converse is not established by such a limit.**

For arbitrary continuous `η`, two distinctions must remain explicit:

- meromorphic continuation is not guaranteed;
- the displayed coefficient can vanish, so \(m\) need not be the actual pole order even when continuation exists.

For example, in one dimension with \(h=0,k=1,\eta(u)=u\), the coefficient at the candidate location \(-1/2\) vanishes, and \(V(z)=1/(2z+2)\) is regular there.

### Nonattainment and `m=0`

This is a **correct and harmless generalization**.

If no coordinate attains \(l\), then every \(A_i>0\), `J` is empty, `faceProj = id`, and `mellinConst = 1`. The theorem becomes
\[
V(-l+s)\to V(-l).
\]
Boundedness of the amplitude and integrability of the residual weight justify this regular-point limit.

Keep the theorem as stated. Merely distinguish this case in the documentation from the attained-minimum, \(m\ge1\), pole interpretation.

### 2. The single Gamma factor

The description is accurate **under the hypotheses of the Laplace-side asymptotic**, including the attained minimum and positive \(\beta\).

The equality theorem itself is an unconditional algebraic identity between definitions. It does not independently derive either asymptotic, nor justify interpreting the identity as a Laplace leading-coefficient statement in the `m=0` case or for arbitrary \(\beta\).

A precise description is:

> The independently proved Abelian limits on the Mellin and Laplace sides have coefficients related by this definitional identity.

“Not Tauberian, not a meromorphic continuation, not a pole theorem” is accurate and appropriately modest.

## Should-fix list

1. **Replace “continuous η on the unit box” by “η extending continuously to the closed unit cube.”**  
   Under the stipulated convention, `unitBox = (0,1]^d`. Continuity there alone neither controls boundary growth nor determines the values `η(πu)` on zero-coordinate faces. Lean’s global continuity supplies exactly the needed boundary control.

2. **Qualify “leading Laurent coefficient itself” for general continuous amplitudes.**  
   Prefer “the real-axis Abelian limit corresponding to the leading Laurent coefficient.” Mention that the limit does not establish continuation or exact pole order and may be zero.

3. **Separate the constant-amplitude product formula from general `η` in the Unit 222 introduction.**  
   Its opening currently introduces an amplitude-weighted transform immediately before displaying the amplitude-independent product formula. Explicitly label that formula **for `η=1`**.

4. **Document the `m=0` case and the scope of the Gamma comparison.**  
   No additional attainment hypothesis is needed in `mellin_leading_tendsto`. The pole and Laplace-leading-coefficient interpretations, however, use the attained-minimum case and the Laplace theorem’s hypotheses.

5. **Narrow Unit 221’s measure-construction wording.**  
   Suggested docstring:
   > “Normalization of the posterior quotient: the posterior mean of `1` is `1`.”

   In the module prose, say the finite positive density **defines** a probability measure, rather than identifying `ncPosteriorMean_one` with a formal measure-construction theorem.

6. **When discussing automatic observable integrability, say “bounded measurable,” not merely “bounded.”**

No mathematical statement change is required in the displayed theorems.

## Suggested mirror replacement

> **Zeta side.** For an amplitude η extending continuously to the closed unit cube, the real-axis Abelian limit corresponding to the leading Laurent coefficient is formalised: [retain the displayed limit and theorem reference]. For η = 1 and λ the attained minimum, this limit is \(a_{-m}\) of (eq:a_minus_m_explicit) at \(b=1\) [mellinCoeff_one]. Under the hypotheses of the Laplace amplitude theorem, its leading constant is exactly \(\Gamma(\lambda)\beta^{-\lambda}/(m-1)!\) times this Mellin coefficient [amplitudeCoeff_eq_gamma_mul_mellinCoeff]. Thus the independently proved Abelian limits recover the paper’s single \(\Gamma(\lambda)\) factor; no Tauberian theorem, meromorphic continuation, or assertion of an exact-order pole for general continuous η is made.

## Sanity checks performed

- Checked the minimizing exponent:
  \[
  2k_i(-l+s)+h_i=-1+2k_i s.
  \]
- Checked the concentrating probability density:
  \[
  (2k_i s)u^{2k_i s-1}\,du.
  \]
- Checked strict residual integrability off `J`: \(h_i-2k_i l>-1\).
- Checked the constant-amplitude product and equal-ratio corner coefficient.
- Checked the regular-point `m=0` reduction.
- Recomputed both numerical examples:
  \[
  sV(-1/2+s)=\frac12\left(\frac1{1+2s}+\frac1{2+2s}\right)\to\frac34,
  \]
  giving approximately `0.643939`, `0.737721`, `0.748752`; and
  \[
  s^2V(-1/2+s)=\frac14+\frac{0.15s}{1+2s}
                            +\frac{0.05s}{1+s}\to\frac14,
  \]
  giving `0.267045`, `0.251966`, `0.250200`.

All supplied numerical checks agree.
