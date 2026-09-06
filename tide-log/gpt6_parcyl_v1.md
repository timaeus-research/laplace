The cleanest route is **scale \(t\) first, then apply the power substitution with exponent \(2\)**. This avoids changing variables directly with a square root.

**Version caveat:** I cannot inspect the v4.33.0 sources here, so I cannot honestly certify the exact argument lists, namespaces, or name changes of the change-of-variables and Gaussian-integrability lemmas. Below, I distinguish the *normalized statements you need* from actual library declarations; I would not treat the displayed wrappers as verbatim Mathlib signatures.

## 1. Change variables by scaling, then squaring

Write
\[
 F(t)=t^{\lambda-1}\exp(-\beta t+\beta a\sqrt t),
 \qquad H(r)=F(r/(2\beta)).
\]

Use the scaling theorem in this normalized form:
```lean
-- Normalized interface, not a verbatim Mathlib declaration:
∫ t in Set.Ioi 0, H (b * t)
  = b⁻¹ * ∫ r in Set.Ioi 0, H r       -- hb : 0 < b
```

This is the interface to obtain from the `integral_comp_mul_left_Ioi` candidate in your question. Instantiate it with **`b := 2 * β` and `H := fun r => F (r / (2 * β))`**. Since
```lean
H ((2 * β) * t) = F t
```
by `field_simp [ne_of_gt hβ]`, it gives
\[
 \int_0^\infty F(t)\,dt
 =(2\beta)^{-1}\int_0^\infty H(r)\,dr.
\]

Next use your power-substitution theorem at **`p := (2 : ℝ)`**:
```lean
-- Normalized interface:
∫ u in Set.Ioi 0, (p * u ^ (p - 1)) • H (u ^ p)
  = ∫ r in Set.Ioi 0, H r
```

**Use this equality backwards** to replace the integral of `H`. Simplifying real scalar multiplication, \(u^{2-1}=u\), and real power \(u^2\) to natural power gives
\[
 S_\lambda
 =(2\beta)^{-1}
   \int_0^\infty (2u)\,
     F\!\left(\frac{u^2}{2\beta}\right)\,du.
\]

Thus the \(2u\) comes from the power substitution, and the \((2\beta)^{-1}\) comes from scaling. Together they are precisely \(u/\beta\).

This order is preferable to first squaring and then scaling \(u\): it requires only one nontrivial square-root identity.

### The pointwise lemma to prove separately

Set
```lean
let K : ℝ → ℝ := fun u =>
  u ^ (2 * lam - 1) *
    Real.exp (-u^2 / 2 + a * Real.sqrt (β / 2) * u)
```

Prove, for `hu : 0 < u`,
```lean
(2 * u) * F (u^2 / (2 * β))
  = (2 * (2 * β) ^ (-(lam - 1))) * K u
```

Then use `integral_congr_ae`, followed by `integral_const_mul`. This produces
```lean
∫ t in Set.Ioi 0, F t
  = ((2 * β) ^ (-(lam - 1)) * β⁻¹) *
      ∫ u in Set.Ioi 0, K u
```
after ordinary field/ring algebra.

For the restricted-domain pointwise reasoning, the usual pattern is:
```lean
apply integral_congr_ae
filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
-- hu : u ∈ Set.Ioi 0, hence hu : 0 < u
```

Do **not** try to establish the integrand identity at negative `u`: both the rpow and square-root simplifications are deliberately restricted to `Ioi 0`.

### Square roots

Use the following two separate identities:
\[
 \sqrt{\frac{u^2}{2\beta}}=\frac{u}{\sqrt{2\beta}},
 \qquad
 \frac{\beta}{\sqrt{2\beta}}=\sqrt{\beta/2}.
\]

For the first, the relevant lemmas are `Real.sqrt_div` and `Real.sqrt_sq`, with `hu.le`. An alternative is `Real.sqrt_sq_eq_abs` followed by `abs_of_pos hu`.

For the second, a particularly convenient bridge is
\[
 \sqrt{2\beta}=2\sqrt{\beta/2}.
\]
Prove this from `Real.sqrt_mul`, normalizing \(2\beta=4(\beta/2)\), or by squaring two nonnegative sides using `Real.sq_sqrt`. Then clear the nonzero denominator and use
```lean
Real.sq_sqrt (show 0 ≤ β / 2 by positivity)
```

Consequently,
```lean
-β * (u^2 / (2 * β)) +
    β * a * Real.sqrt (u^2 / (2 * β))
  =
-u^2 / 2 + a * Real.sqrt (β / 2) * u
```
is just field/ring algebra after rewriting those identities.

### Real powers

The power part is exactly
\[
 u\left(\frac{u^2}{2\beta}\right)^{\lambda-1}
 =(2\beta)^{-(\lambda-1)}u^{2\lambda-1}.
\]

The relevant rewrite chain uses:

- `Real.div_rpow`;
- `Real.rpow_natCast` to bridge natural powers and real powers;
- `Real.rpow_mul` to turn \((u^2)^{\lambda-1}\) into \(u^{2(\lambda-1)}\);
- `Real.rpow_neg` to replace reciprocal powers;
- `Real.rpow_add` to combine \(u^1u^{2(\lambda-1)}\);
- `ring` for the exponent identity \(1+2(\lambda-1)=2\lambda-1\).

Keep `hu : 0 < u` and `h2β : 0 < 2 * β` available. Normalize the exponents explicitly with `have ... := by ring`; do not expect `ring` to recognize equal rpow expressions without first rewriting their exponents.

## 2. Which direction?

I would prove this intermediate result:
```lean
theorem fluctuation_eq_kernel
    (hβ : 0 < β) :
    fluctuation β lam a =
      ((2 : ℝ) ^ (1 - lam) * β ^ (-lam)) *
        ∫ u in Set.Ioi 0,
          u ^ (2 * lam - 1) *
            Real.exp (-u^2 / 2 + a * Real.sqrt (β / 2) * u) := by
  ...
```

Then unfold `parCylNeg` and finish algebraically.

This direction keeps all change-of-variables work separate from Gamma. In particular, **`hlam` is not needed for the pointwise substitution algebra or constant identity**. It is needed for the kernel’s integrability and for the convenient proof that `Real.Gamma (2 * lam) ≠ 0`.

Mathlib’s set integrals are totalized Bochner integrals, so do not add integrability hypotheses merely for `integral_const_mul` or `integral_congr_ae`. Whether a particular change-of-variables declaration requires an integrability hypothesis must be checked in its actual signature.

## 3. Integrability: your domination is the right one

Your estimate is correct:
\[
 -u^2/2-xu\le x^2-u^2/4,
\]
and its Lean proof is pleasantly short:
```lean
have hexponent :
    -u^2 / 2 - x * u ≤ x^2 - u^2 / 4 := by
  nlinarith [sq_nonneg (u / 2 + x)]
```

The Gaussian comparison function is
```lean
fun u : ℝ =>
  u ^ (ν - 1) *
    Real.exp (-(1 / 4 : ℝ) * u ^ (2 : ℝ))
```

For the generalized Gaussian-integrability result, the mathematical hypotheses to supply are
```lean
-1 < ν - 1
0 < (2 : ℝ)
0 < (1 / 4 : ℝ)
```
proved by `linarith` and `norm_num`. I cannot certify that these hypotheses are named `hs`, `hp`, and `hb` in the v4.33 declaration, or their exact ordering.

**There is no substantive npow/rpow obstruction.** The difference is:
```lean
u ^ (2 : ℝ)  -- Real.rpow
u ^ (2 : ℕ)  -- natural power
```
and `Real.rpow_natCast` bridges them. Normalize this once before doing the polynomial exponent inequality.

Your domination proof then has this structure:
```lean
-- μ := volume.restrict (Set.Ioi (0 : ℝ))
-- hGaussian : Integrable gaussian μ
have hmajorant := hGaussian.const_mul (Real.exp (x^2))

apply hmajorant.mono'
· -- AEStronglyMeasurable target μ
  -- Prove global measurability by `fun_prop`, then use
  -- Measurable.aestronglyMeasurable.
  ...
· filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hpow : 0 ≤ u ^ (ν - 1) :=
    Real.rpow_nonneg hu.le _
  -- Remove the norm using nonnegativity.
  -- Apply Real.exp_le_exp.mpr hexponent.
  -- Multiply by hpow.
  -- Rewrite exp(x² - u²/4) using Real.exp_add.
  ...
```

Two details matter:

1. `Integrable.mono'` also requires strong measurability; the majorization alone is insufficient.
2. On `Ioi 0`, both the target and majorant are nonnegative, so their norm bookkeeping is trivial.

This is cleaner than splitting the domain into a neighborhood of zero and a tail.

## 4. Constants

For the rpow constant, isolate the cancellation involving `β`:

```lean
have hβpow :
    β ^ (1 - lam) * β⁻¹ = β ^ (-lam) := by
  calc
    β ^ (1 - lam) * β⁻¹
        = (β ^ (-lam) * β) * β⁻¹ := by
            rw [show 1 - lam = -lam + 1 by ring,
              Real.rpow_add hβ, Real.rpow_one]
    _ = β ^ (-lam) := by
      simp [mul_assoc, ne_of_gt hβ]
```

Then:
```lean
have hconstant :
    (2 * β) ^ (-(lam - 1)) * β⁻¹
      = (2 : ℝ) ^ (1 - lam) * β ^ (-lam) := by
  calc
    (2 * β) ^ (-(lam - 1)) * β⁻¹
        = (2 : ℝ) ^ (1 - lam) *
            (β ^ (1 - lam) * β⁻¹) := by
              rw [show -(lam - 1) = 1 - lam by ring,
                Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hβ.le]
              ring
    _ = _ := by rw [hβpow]
```

This illustrates the right division of labor: **rpow rewrites first; `ring` and `field_simp` afterwards**.

### Final Gamma/exponential cancellation

Let
\[
 q=\beta a^2/8,\quad
 J=\int_0^\infty K(u)\,du,\quad
 C=2^{1-\lambda}\beta^{-\lambda}.
\]

After unfolding `parCylNeg`, establish
\[
 \operatorname{parCylNeg}(2\lambda,-a\sqrt{\beta/2})
   =\frac{e^{-q}}{\Gamma(2\lambda)}J.
\]

The square identity needed here follows by rewriting
```lean
Real.sq_sqrt (show 0 ≤ β / 2 by positivity)
```
and then using `ring`. The kernel’s linear term is a separate `ring` normalization under `Real.exp`.

Use:
```lean
have hΓ : Real.Gamma (2 * lam) ≠ 0 :=
  ne_of_gt (Real.Gamma_pos_of_pos (by linarith))

have hexp :
    Real.exp q * Real.exp (-q) = 1 := by
  rw [← Real.exp_add]
  simp
```

The remaining equality is simply
\[
 CJ=C\,\Gamma(2\lambda)e^q
       \left(\frac{e^{-q}}{\Gamma(2\lambda)}J\right).
\]
Reassociate, cancel Gamma using `hΓ`, and rewrite `hexp`. **You never need to divide by \(J\)** or prove that the kernel integral is nonzero.

In short: use the specialized **positive scaling theorem**, then **`integral_comp_rpow_Ioi_of_pos` backwards at \(p=2\)**; prove one pointwise kernel identity; and leave Gamma entirely out of the substitution proof. I cannot responsibly flag any v4.33 name changes without checking that version’s declarations.