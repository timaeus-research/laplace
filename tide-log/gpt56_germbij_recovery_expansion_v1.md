1. **Taylor remainder lemma A**

I do not know of a Mathlib v4.29.0 theorem giving this bound for all `s ≥ 0`. The local lemmas such as `Real.abs_exp_sub_one_sub_id_le` are restricted to a bounded interval.

You can avoid inverses entirely. This is cleaner than the `(1+s)⁻¹` argument in Lean:

```lean
lemma abs_exp_neg_sub_one_add_le_sq {s : ℝ} (hs : 0 ≤ s) :
    |Real.exp (-s) - 1 + s| ≤ s ^ 2 := by
  have hlo : 0 ≤ Real.exp (-s) - 1 + s := by
    have h := Real.add_one_le_exp (-s)
    linarith

  have hmul : Real.exp (-s) * (1 + s) ≤ 1 := by
    have h :=
      mul_le_mul_of_nonneg_right
        (Real.add_one_le_exp s) (Real.exp_pos (-s)).le
    calc
      Real.exp (-s) * (1 + s)
          = (s + 1) * Real.exp (-s) := by ring
      _ ≤ Real.exp s * Real.exp (-s) := h
      _ = 1 := by
        rw [← Real.exp_add]
        simp

  have hu : 0 < 1 + s := by linarith

  have hhi : Real.exp (-s) - 1 + s ≤ s ^ 2 := by
    apply (mul_le_mul_right hu).mp
    nlinarith [sq_nonneg s]

  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg s]
  · exact hhi
```

The only part that may need a small syntactic adjustment is the orientation/order in `hmul`, depending on simplification. The argument itself is robust:

\[
e^{-s}(1+s)\le e^{-s}e^s=1.
\]

I would prefer this multiplication proof over inverse-order lemmas: it avoids locating the current names and side-condition conventions for `inv_le_inv₀`/`one_div_le_one_div_of_le`.

A stronger helper is also useful:

```lean
lemma exp_neg_sub_one_add_bounds {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ Real.exp (-s) - 1 + s ∧
      Real.exp (-s) - 1 + s ≤ s ^ 2 := ...
```

Then derive the absolute-value version as a corollary. The lower bound later shows that the quartic expansion error is actually nonnegative.

---

2. **Dominated remainder and the integral inequality**

Use

```lean
q x := Real.exp (-(t * x ^ 2) / 2)
s x := t * b * x ^ 4
r x := Real.exp (-(s x)) - 1 + s x
f x := q x * r x
g x := (t * b) ^ 2 * x ^ 8 * q x
```

Then `A` and positivity give

```lean
‖f x‖ ≤ g x
```

after `simp [f, g, q, s, r, Real.norm_eq_abs]` and `ring_nf`/`nlinarith`.

The standard robust chain for

\[
\left\|\int f\right\| \le \int g
\]

is:

```lean
have hg : Integrable g := by
  -- scalar multiple of the k = 4 Gaussian moment integrand
  ...

have hf_meas : AEStronglyMeasurable f := by
  -- all functions involved are continuous
  exact (...).aestronglyMeasurable

have hdom : ∀ᵐ x, ‖f x‖ ≤ g x :=
  Filter.Eventually.of_forall fun x => by
    ...

have hg_nonneg : ∀ᵐ x, 0 ≤ g x :=
  Filter.Eventually.of_forall fun x => by
    positivity

have hf : Integrable f := by
  apply hg.mono' hf_meas
  filter_upwards [hdom, hg_nonneg] with x hfg hg0
  simpa [Real.norm_eq_abs, abs_of_nonneg hg0] using hfg

have hint :
    ‖∫ x, f x‖ ≤ ∫ x, g x := by
  calc
    ‖∫ x, f x‖ ≤ ∫ x, ‖f x‖ :=
      norm_integral_le_integral_norm f
    _ ≤ ∫ x, g x :=
      integral_mono_ae hf.norm hg hdom
```

For real-valued `f`, finish with `simpa [Real.norm_eq_abs] using hint`.

The exact signature of `Integrable.mono'` may expect the domination as `‖f x‖ ≤ ‖g x‖`. If so, use `hg_nonneg` to simplify `‖g x‖` to `g x`. This is the only mild API-sensitive point.

There may also be a direct `norm_integral_le_of_norm_le` lemma, but the explicit chain above is easier to debug and makes the required integrability clear.

### Integrability organization

You need:

* `q`, from the `k = 0` Gaussian family;
* `x ^ 4 * q x`, from `k = 2`;
* `g`, from `k = 4`;
* `f`, by domination with `g`.

You do **not** need a separate difficult proof for the original quartic integrand if you first prove a pointwise decomposition and then integrate the decomposed expression. Alternatively, the original integrand is directly dominated by `q`, since `b ≥ 0`, `t > 0`, and hence `exp (-(t*b*x^4)) ≤ 1`.

Also note that at `k = 0`, the expression `(2*k - 1)‼` uses natural subtraction, so it simplifies to `0‼ = 1`; there is no actual negative natural double factorial to handle.

---

3. **Exponential grouping**

Normalize the exponent once in a pointwise helper. Do not rely on `simp` to see through all the multiplication and division:

```lean
have hexp_split (x : ℝ) :
    Real.exp (-(t * (x ^ 2 / 2 + b * x ^ 4))) =
      Real.exp (-(t * x ^ 2) / 2) *
        Real.exp (-(t * b * x ^ 4)) := by
  rw [show -(t * (x ^ 2 / 2 + b * x ^ 4)) =
      -(t * x ^ 2) / 2 + -(t * b * x ^ 4) by ring]
  rw [Real.exp_add]
```

Depending on the normal form produced by your definition, the right exponent may be written `-(t * b * x ^ 4)` or `-(t * (b * x ^ 4))`; `ring` handles either.

Then establish the exact pointwise expansion:

```lean
q x * Real.exp (-(t * b * x ^ 4))
  = q x * (1 - t * b * x ^ 4) + f x
```

with `ring` after unfolding `f` and `r`.

This is substantially more reliable than repeatedly asking `congr`/`simp` to normalize under `Real.exp`.

For the `Real.rpow` arithmetic, isolate small helper identities rather than asking `ring` to handle them:

```lean
have ht_ne : t ≠ 0 := ne_of_gt ht

have ht_mul :
    t * t ^ (-(5 : ℝ) / 2) = t ^ (-(3 : ℝ) / 2) := by
  -- use Real.rpow_add with ht.le/ht, then normalize exponents
  ...

have ht_sq_mul :
    t ^ 2 * t ^ (-(9 : ℝ) / 2) = t ^ (-(5 : ℝ) / 2) := by
  ...
```

`ring` can normalize the exponents after `Real.rpow_add`, but it does not itself know the multiplicative laws of `Real.rpow`.

---

4. **Statement shapes**

### B: keep an absolute-value theorem, but consider proving a stronger internal result

The remainder is nonnegative, so the strongest natural statement is

```lean
0 ≤
  partitionFunction (fun x ↦ x^2 / 2 + b * x^4) t
    - √(2 * Real.pi) * t ^ (-(1 : ℝ) / 2)
    + 3 * b * √(2 * Real.pi) * t ^ (-(3 : ℝ) / 2)
```

together with the stated upper bound.

I would implement:

```lean
theorem quartic_partition_expansion_bounds ... :
    0 ≤ E b t ∧
    E b t ≤ 105 * b^2 * √(2 * Real.pi) * t ^ (-(5 : ℝ) / 2)
```

and expose the requested convenient corollary:

```lean
theorem quartic_partition_expansion ... :
    |E b t| ≤
      105 * b^2 * √(2 * Real.pi) * t ^ (-(5 : ℝ) / 2)
```

The absolute-value form is ideal for C and for later asymptotic use; the two-sided helper records the stronger fact essentially for free.

### C: explicit tail equality versus `EventuallyEq`

The idiomatic Mathlib statement is:

```lean
(h : (fun t => Z b₁ t) =ᶠ[Filter.atTop] fun t => Z b₂ t)
```

Positivity of `t` is then automatic eventually. It also avoids carrying `T` and `hT`.

The explicit version

```lean
∀ t, T ≤ t → Z b₁ t = Z b₂ t
```

is easier to use if the surrounding repository consistently states tail hypotheses that way. A good compromise is:

* prove the theorem using `EventuallyEq`;
* provide an explicit-`T` wrapper.

### `IsLittleO`

The stronger recovery principle is indeed:

```lean
Z b₁ t - Z b₂ t = o(t ^ (-(3 : ℝ) / 2))
```

at `atTop`, which forces `b₁ = b₂`. This is mathematically more general than eventual equality, but it introduces considerably more filter and `Real.rpow` asymptotic API.

For the first recovery theorem, I recommend direct eventual equality. Add an `IsLittleO` version later, preferably after proving a reusable asymptotic statement such as

\[
t^{3/2}\left(Z_b(t)-\sqrt{2\pi}\,t^{-1/2}\right)
\to -3b\sqrt{2\pi}.
\]

---

5. **A simpler recovery candidate**

There is a much simpler non-expansion recovery: for any fixed `t > 0`, the partition function is strictly decreasing in `b ≥ 0`.

If `b₁ < b₂`, then for every `x ≠ 0`,

\[
e^{-t(x^2/2+b_2x^4)}
<
e^{-t(x^2/2+b_1x^4)}.
\]

Since this strict inequality holds on a positive-measure set and both functions are integrable, their integrals are strictly ordered. Thus equality at just one positive `t` implies `b₁=b₂`.

That is the minimal injectivity theorem. However, it does **not** implement the Section 7.4 “subleading asymptotic pairing” mechanism. If this thread is specifically intended to establish expansion-based recovery, A+B+C remain the right development even though direct monotonicity is shorter.

For C’s direct Archimedean finish, it is often easiest to first derive

\[
3|b_1-b_2|\,t \le 105(b_1^2+b_2^2)
\]

for every sufficiently large positive `t`. If `b₁ ≠ b₂`, instantiate it at something like

\[
t=T+1+\frac{35(b_1^2+b_2^2)}{|b_1-b_2|},
\]

then discharge the contradiction with positivity and `nlinarith`/`field_simp`. This avoids setting up limits.

---

6. **File organization**

Yes: put A, B, and C together initially in

```text
Laplace/OneD/RecoveryExpansion.lean
```

Suggested order:

1. elementary exponential remainder bounds;
2. local definitions/helper identities for the quartic remainder;
3. `quartic_partition_expansion_bounds`;
4. absolute-value expansion corollary;
5. eventual-equality recovery;
6. optional explicit-tail wrapper.

If A later has another user, move it to a small general analytic inequalities file. For the first implementation, keeping the entire proof chain in one file will make imports and API adjustments much easier.