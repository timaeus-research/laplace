## 1. Candidate A

Yes, A is mathematically correct as stated. There is no degeneracy from arbitrary or negative `T`.

With

```lean
let t₀ : ℝ := max T 2
```

you have:

```lean
1 < t₀
T ≤ t₀
T ≤ t₀ ^ (2 : ℝ)
```

The last fact follows from `2 ≤ t₀`, hence `t₀ ≤ t₀ ^ 2`.

A slightly easier proof than introducing `β₁ - β₂` is:

1. Evaluate at `t₀`:
   \[
   \alpha_1 u_1=\alpha_2u_2,\qquad u_i=t₀^{\beta_i}.
   \]
2. Evaluate at `t₀ ^ (2 : ℝ)` and rewrite using `Real.rpow_mul`:
   \[
   \alpha_1u_1^2=\alpha_2u_2^2.
   \]
3. All `αᵢ,uᵢ` are positive. Cancelling the first equality from the second gives `u₁ = u₂`.
4. Injectivity of `β ↦ t₀ ^ β`, since `1 < t₀`, gives `β₁ = β₂`.
5. Substitute and cancel the positive factor `t₀ ^ β₁` to get `α₁ = α₂`.

This avoids `Real.rpow_sub` and most division normalization.

You could even weaken A to equality only at those two selected points, but the eventual formulation is the useful interface.

---

## 2. Relevant Mathlib API

The stable and convenient way to obtain exponent injectivity is:

```lean
#check Real.strictMono_rpow_of_base_gt_one
```

Conceptually its signature is:

```lean
Real.strictMono_rpow_of_base_gt_one {b : ℝ} (hb : 1 < b) :
  StrictMono (fun y : ℝ ↦ b ^ y)
```

Thus:

```lean
have hβ : β₁ = β₂ :=
  (Real.strictMono_rpow_of_base_gt_one ht₀).injective hpow
```

This is preferable to relying on the potentially confusing left/right naming of an injectivity lemma.

### Injectivity in the base

For a positive exponent:

```lean
#check Real.strictMonoOn_rpow_of_pos
```

Conceptually:

```lean
Real.strictMonoOn_rpow_of_pos {c : ℝ} (hc : 0 < c) :
  StrictMonoOn (fun x : ℝ ↦ x ^ c) (Set.Ici 0)
```

Hence, for `0 < a₁`, `0 < a₂`:

```lean
have : a₁ = a₂ :=
  (Real.strictMonoOn_rpow_of_pos hc).injOn ha₁.le ha₂.le hpow
```

For a negative exponent, the corresponding lemma is:

```lean
#check Real.strictAntiOn_rpow_of_neg
```

so a general nonzero-exponent helper can split on `c < 0 ∨ 0 < c`.

For C, however, it is cleaner to arrange that the base-injectivity step uses the positive exponent

```lean
q = 1 / (2 * k : ℝ)
```

rather than the negative exponent `-q`.

### `Real.rpow_mul`

The useful orientation is:

```lean
Real.rpow_mul (hx : 0 ≤ x) (y z : ℝ) :
  x ^ (y * z) = (x ^ y) ^ z
```

Therefore:

```lean
have hsq :
    (t₀ ^ (2 : ℝ)) ^ β = t₀ ^ ((2 : ℝ) * β) := by
  symm
  exact Real.rpow_mul ht₀.le (2 : ℝ) β
```

No `Real.rpow_natCast` is needed if you consistently use `(2 : ℝ)`.

If you mix natural powers and `rpow`, `Real.rpow_natCast` is the bridge, with a nonnegativity hypothesis on the base. Avoiding that mixture is simpler here.

---

## 3. Candidate C and factorization pitfalls

There is no mathematical problem with

\[
\left(\frac{(2k)!}{at}\right)^q
=
((2k)!)^q\,a^{-q}\,t^{-q}
\]

provided the relevant quantities are positive. Here:

- `(2k)! > 0`,
- `a > 0`,
- `t > 0`,
- `q = 1/(2k) > 0`.

The Lean issue is mainly syntactic: normalizing all the way to three multiplicative `rpow` factors can require several applications of:

```lean
Real.div_rpow
Real.mul_rpow
Real.rpow_neg
```

together with nonnegativity/positivity side conditions and reassociation.

A cleaner coefficient is

\[
\alpha(k,a)
=
\frac1k\,
\Gamma(q)\,
\left(\frac{(2k)!}{a}\right)^q,
\qquad
q=\frac1{2k}.
\]

Then only prove

\[
\left(\frac{(2k)!}{at}\right)^q
=
\left(\frac{(2k)!}{a}\right)^q t^{-q},
\]

using

\[
\frac{(2k)!}{at}
=
\frac{(2k)!/a}{t}.
\]

This requires one division-rpow normalization rather than fully splitting the factorial, `a`, and `t`.

After A gives equality of the coefficients and `k₁ = k₂`, cancel the common positive factors to get

\[
\left(\frac{N}{a_1}\right)^q
=
\left(\frac{N}{a_2}\right)^q,
\qquad N=(2k)!.
\]

Since `q > 0`, use:

```lean
(Real.strictMonoOn_rpow_of_pos hq).injOn
```

to conclude:

\[
N/a_1=N/a_2,
\]

and then cancel `N > 0` to obtain `a₁ = a₂`.

This avoids needing injectivity for the negative exponent entirely.

Useful positivity facts will include something along the lines of:

```lean
Nat.factorial_pos _
Real.Gamma_pos_of_pos hq
Real.rpow_pos_of_pos hbase _
```

with casts handled by `positivity` or `exact_mod_cast`.

### Recovering `k`

From A you get:

\[
-\frac1{2k_1}=-\frac1{2k_2}.
\]

First remove the minus signs, then clear the positive/nonzero denominators. In Lean, `field_simp` plus positivity/nonzeroness of `kᵢ` is often simpler than searching for a specialized inverse-injectivity lemma. Finish the cast step with `exact_mod_cast` or `Nat.cast_injective`.

---

## 4. A better minimal route

The best simplification is:

1. Keep A.
2. Keep B.
3. In C, define
   ```lean
   q k := 1 / (2 * (k : ℝ))
   ```
   and use
   ```lean
   α k a :=
     (1 / (k : ℝ)) *
       Real.Gamma (q k) *
       (((Nat.factorial (2 * k) : ℕ) : ℝ) / a) ^ (q k)
   ```
   up to whatever multiplication order matches the existing theorem.
4. Rewrite the partition function as
   ```lean
   α k a * t ^ (-(q k))
   ```
   without splitting `((2*k)!)^q` from `a^-q`.
5. Apply A.
6. Recover `k`.
7. Recover `a` using positive-exponent base injectivity on `(((2*k)! : ℝ) / a) ^ q`.

This minimizes the amount of `rpow` algebra substantially.

Also, `T > 0` is convenient but not logically necessary. If `T` is arbitrary, restrict the equality to the positive tail beginning at `max T 1`; the closed form is then applicable. Keeping `T > 0` makes the corollary statement and proof simpler.

---

## 5. Vote

Yes: **A + B + C** is a coherent minimal constructive-recovery file.

Suggested organization:

1. Generic analytic lemma A, preferably outside the seabed-specific namespace.
2. `partitionFunction_smul` next to the definition of `partitionFunction`.
3. The `kthPotential` recovery theorem in the tide/recovery namespace.
4. Optionally one small helper for injectivity of `x ↦ x ^ c` on positive reals, although C can avoid it by using the positive exponent `q`.

For B, the proof should indeed be essentially:

```lean
by
  unfold partitionFunction
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  congr 1
  ring
```

possibly with a slightly different `congr` shape depending on the exact definition of `partitionFunction`.