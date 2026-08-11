Yes: the stated `∀ N` estimate is the right quantitative core. I would prove that first and add the repository’s superpolynomial/`IsLittleO` formulation as a short corollary.

## 1. Statement shape

For this theorem, the even-power formulation composes better with the Gaussian moments:

```lean
(hflat :
  ∀ n : ℕ, ∃ C δ : ℝ,
    0 ≤ C ∧ 0 < δ ∧
    ∀ x, |x| ≤ δ → f x ≤ C * x ^ (2 * n))
```

Advantages:

- `x ^ (2 * n)` is nonnegative without introducing `Real.rpow`.
- It plugs directly into even Gaussian moment lemmas.
- The global domination argument stays in ordinary natural powers.
- It is exactly what this proof needs.

A more general reusable notion of flatness would conventionally use

```lean
|f x| ≤ C * |x| ^ n
```

but here `0 ≤ f`, and you only consume even orders. I would keep the theorem’s hypothesis in the even-power form, possibly with a separate conversion helper from a standard flatness predicate.

I suggest an explicit statement along these lines:

```lean
theorem flat_perturbation_invisible
    {f φ : ℝ → ℝ} {M : ℝ}
    (hf_c : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x)
    (hM : 0 ≤ M)
    (hf_bdd : ∀ x, f x ≤ M)
    (hflat :
      ∀ n : ℕ, ∃ C δ : ℝ,
        0 ≤ C ∧ 0 < δ ∧
        ∀ x, |x| ≤ δ → f x ≤ C * x ^ (2 * n))
    (hφ_c : Continuous φ)
    (hφ_s : HasCompactSupport φ) :
    ∀ N : ℕ, ∃ K T : ℝ,
      0 ≤ K ∧ 1 ≤ T ∧
      ∀ t, T ≤ t →
        |(∫ x, φ x * Real.exp (-(t * (x ^ 2 / 2))))
          - (∫ x, φ x * Real.exp (-(t * (x ^ 2 / 2 + f x))))|
          ≤ K / t ^ N
```

The all-orders `O(t⁻ᴺ)` statement faithfully captures “no asymptotic expansion coefficient changes.” Moreover, by applying the estimate at `N + 1`, it implies the corresponding `IsLittleO` statement at order `N`. Thus I would make:

1. this theorem the elementary quantitative result;
2. a short corollary translating it into `Laplace.Decay`’s superpolynomial vocabulary.

That keeps the analytic proof independent of the packaging.

## 2. Integral comparison and compact support

Let

```lean
F t x := φ x * exp (-(t * (x ^ 2 / 2)))
G t x := φ x * exp (-(t * (x ^ 2 / 2 + f x)))
```

Both are continuous. Their compact support follows because multiplication by the exponential factor cannot enlarge the support beyond that of `φ`.

The intended pattern should be approximately:

```lean
have hF_cont : Continuous (F t) := ...
have hF_comp : HasCompactSupport (F t) :=
  hφ_s.mul_right _
have hF_int : Integrable (F t) :=
  hF_cont.integrable_of_hasCompactSupport hF_comp
```

and similarly for `G`. For the expression `φ * exponential`, `mul_right` is the semantically expected orientation: the compactly supported function is on the left and the arbitrary multiplier is on the right. If the pointwise-function instance causes an elaboration issue, writing the functions explicitly or supplying the multiplier argument usually resolves it.

The robust comparison chain is:

```lean
calc
  |∫ x, F t x - ∫ x, G t x|
      = ‖∫ x, F t x - G t x‖ := by
          rw [integral_sub hF_int hG_int]
          rfl
  _ ≤ ∫ x, ‖F t x - G t x‖ :=
        norm_integral_le_integral_norm _
  _ ≤ ∫ x, H t x := by
        apply integral_mono
        · exact (hF_int.sub hG_int).norm
        · exact hH_int
        · intro x
          exact hpointwise x
```

Depending on the exact v4.29 signature, the final step may be more convenient as `integral_mono_ae` with `Filter.Eventually.of_forall hpointwise`.

Thus the two original integrability obligations really are free from continuity plus compact support. Only the Gaussian comparison function needs a separate integrability proof.

For the pointwise exponential estimate, with `0 ≤ t` and `0 ≤ f x`:

\[
0\le 1-e^{-t f(x)}\le t f(x).
\]

The upper bound follows from `add_one_le_exp (-t * f x)` after linear arithmetic. The lower bound follows from monotonicity of `exp`, since `-t*f x ≤ 0`.

## 3. A global bound for `φ`

Conceptually, the clean fact is:

> A continuous compactly supported function into `ℝ` has bounded range.

If there is a packaged lemma in the imported topology files giving bounded range from `Continuous` and `HasCompactSupport`, use it. The exact names around compactly supported bounded functions have changed across Mathlib versions, so I would not structure the proof around a guessed `bddAbove` lemma.

A stable manual proof is:

1. `tsupport φ` is compact by `hφ_s`;
2. its image under `fun x ↦ |φ x|` is compact because `abs ∘ φ` is continuous;
3. hence that image is bounded;
4. outside `tsupport φ`, `φ x = 0`.

This yields

```lean
∃ B : ℝ, 0 ≤ B ∧ ∀ x, |φ x| ≤ B
```

and is worth extracting as a local or repository helper, e.g.

```lean
exists_abs_le_of_continuous_of_hasCompactSupport
```

A possibly cleaner route, if available in v4.29, is to establish that the entire range of `φ` is compact: it is the image of `tsupport φ`, together with at most `{0}`. Compactness of the whole range immediately gives boundedness without splitting every later argument into support/outside-support cases.

I would return `0 ≤ B` as part of the helper; this simplifies nonnegativity of the Gaussian majorant.

## 4. Global domination and power algebra

### Global domination

Your argument is correct. I would isolate it as a helper:

```lean
lemma exists_global_even_power_bound
    {f : ℝ → ℝ} {M C δ : ℝ} {n : ℕ}
    (hf0 : ∀ x, 0 ≤ f x)
    (hM : 0 ≤ M)
    (hfM : ∀ x, f x ≤ M)
    (hC : 0 ≤ C)
    (hδ : 0 < δ)
    (hloc : ∀ x, |x| ≤ δ → f x ≤ C * x ^ (2 * n)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, f x ≤ A * x ^ (2 * n)
```

For `n = N + 1`, take

```lean
D := M / δ ^ (2 * n)
A := C + D
```

The outside case uses:

```lean
δ < |x|
δ ^ (2 * n) ≤ |x| ^ (2 * n)
|x| ^ (2 * n) = x ^ (2 * n)
```

and hence

```lean
M ≤ (M / δ ^ (2 * n)) * x ^ (2 * n).
```

The main Lean nuisance is not mathematics but cancellation through the positive denominator. It is generally easier to first establish

```lean
0 < δ ^ (2 * n)
```

and then use a division comparison lemma, rather than aggressively `field_simp`.

There is no issue at `x = 0`: the outside branch cannot occur because `δ > 0`.

Strictly speaking, `hf0` is not needed by this global-bound helper if the local and global upper bounds are already given. It is, however, needed elsewhere for the exponential estimate.

### Avoid leaking `rpow` into the main theorem

With `m = N + 1`, the moment gives

\[
\int_{\mathbb R}x^{2m}e^{-t x^2/2}\,dx
 = c_m\,t^{-(m+1/2)}
 = c_m\,t^{-(N+3/2)}.
\]

After multiplying by `t`, this is

\[
c_m\,t^{-(N+1/2)}\le c_m\,t^{-N}
\qquad(t\ge1).
\]

This is mathematically straightforward but can produce disproportionately unpleasant `Real.rpow` algebra.

I recommend adding or proving locally a wrapper around the closed-form moment lemma:

```lean
lemma mul_integral_even_pow_mul_exp_neg_sq_half_le_div_pow
    (N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ t : ℝ, 1 ≤ t →
        t * (∫ x : ℝ,
          x ^ (2 * (N + 1)) * Real.exp (-(t * x ^ 2 / 2)))
          ≤ A / t ^ N
```

Then `flat_perturbation_invisible` remains entirely in ordinary powers.

Inside that helper, the bridge should proceed in two stages:

1. weaken the half-integer exponent to an integer exponent using `1 ≤ t`;
2. only then rewrite the integer `rpow` as `t ^ k` or `1 / t ^ k`.

That is considerably easier than directly normalizing

```lean
t * t ^ (-(N + 3 / 2 : ℝ))
```

to an expression involving `t ^ N`.

The useful API is in the `Real.rpow_*` family—especially monotonicity in the exponent for base at least one, `Real.rpow_natCast`, and a negative-exponent rewrite—but I would verify exact signatures with `#check` in v4.29 before committing names. Encapsulating this in one helper also insulates the main proof from API churn.

You can take `T = 1`. There is no analytic need for a larger threshold unless an existing Gaussian lemma is stated with a stronger positivity assumption.

## 5. File and witness

My vote:

```text
Laplace/OneD/FlatInvisible.lean
```

with:

1. a boundedness helper for continuous compactly supported real functions, unless one already exists;
2. the local-to-global even-power domination helper;
3. the Gaussian-moment-to-plain-power wrapper;
4. `flat_perturbation_invisible`;
5. optionally, a superpolynomial/`IsLittleO` corollary.

I would not put the classic witness in the same initial declaration unless the note explicitly needs it immediately. It is a useful second theorem/example, but its continuity and flatness proof may be longer and more API-sensitive than the core perturbation theorem.

For

```lean
f x := if x = 0 then 0 else Real.exp (-(1 / x ^ 2))
```

one can in fact obtain the flat bound globally:

\[
e^{-1/x^2}\le n!\,x^{2n}.
\]

Set \(s=1/x^2\). From

\[
\frac{s^n}{n!}\le e^s
\]

one gets

\[
e^{-s}\le \frac{n!}{s^n}=n!x^{2n}.
\]

Thus one may take `C = n.factorial` and any positive `δ`, for example `δ = 1`.

`Real.sum_le_exp_of_nonneg` is the likely useful theorem in this Mathlib generation: use the nonnegative `n`th summand’s bound by the finite sum, then bound the finite sum by `exp`. I would verify with:

```lean
#check Real.sum_le_exp_of_nonneg
#check Real.sum_div_factorial_le_exp
```

rather than depend on a guessed direct theorem such as `pow_div_factorial_le_exp`. Even if no direct termwise lemma exists, the finite-sum argument is elementary and stable.

Overall, the proof plan is sound. The two pieces most worth isolating are the local-to-global polynomial bound and the half-integer Gaussian-moment-to-plain-`pow` estimate; doing so should leave the main theorem short and readable.