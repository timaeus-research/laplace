Overall, the C3 shape is sound. The scaling exponents and quotient bookkeeping are correct, subject to making the natural-number subtraction side conditions explicit.

## 1. Exponents and jet interface

### Unnormalized estimate

On the inner region, with \(t=q^{-2}\),

\[
|x|^s |e^{-tK_1(x)}-e^{-tK_2(x)}|
 \le \varepsilon\, t\, |x|^{s+D} e^{-t\rho x^2},
\]

where \(\rho=\min(\rho_1,\rho_2)\). Gaussian scaling gives

\[
\int_{\mathbb R}|x|^{s+D}e^{-q^{-2}\rho x^2}\,dx
 = C_{\rho,s,D}\,q^{s+D+1}.
\]

Multiplication by \(t=q^{-2}\) therefore gives

\[
|A_s(K_1,q)-A_s(K_2,q)|
 \le \varepsilon C_{\rho,s,D}q^{s+D-1}
     + \text{outer error}.
\]

Thus

\[
A_s(K_1,q)-A_s(K_2,q)=o(q^{s+D-1})
\]

is exactly right.

### Quotient estimate

Writing \(Z_i=A_0(K_i,q)\),

\[
\frac{A_{s,1}}{Z_1}-\frac{A_{s,2}}{Z_2}
=
\frac{A_{s,1}-A_{s,2}}{Z_1}
+
\frac{A_{s,2}(Z_2-Z_1)}{Z_1Z_2},
\]

the two terms are respectively

\[
\frac{o(q^{s+D-1})}{\Omega(q)}
=o(q^{s+D-2})
\]

and

\[
\frac{O(q^{s+1})\,o(q^{D-1})}{\Omega(q^2)}
=o(q^{s+D-2}).
\]

So the normalized exponent \(s+D-2\) is also correct.

### Important Lean issue: `Nat` subtraction

If `s D : ℕ`, then

```lean
q ^ (s + D - 1)
q ^ (s + D - 2)
```

use truncated natural subtraction. I recommend explicitly assuming at least:

```lean
1 ≤ s + D
2 ≤ s + D
```

for the respective theorems. In the likely application, a global assumption `2 ≤ D` removes this issue for every `s`.

Alternatively, subtraction-free formulations are robust:

```lean
(A_s K1 q - A_s K2 q) * q / q ^ (s + D) → 0
(F_s K1 q - F_s K2 q) * q ^ 2 / q ^ (s + D) → 0
```

on `q > 0`, but these are less pleasant for consumers. I would use the conventional powers plus side conditions.

### `hjet`: epsilon form versus `IsLittleO`

Your epsilon form is mathematically the right condition:

```lean
∀ ε > 0, ∃ δ > 0, ∀ x,
  |x| ≤ δ → |K1 x - K2 x| ≤ ε * |x| ^ D
```

It is essentially the concrete one-dimensional expansion of

```lean
IsLittleO
  (fun x : ℝ => K1 x - K2 x)
  (fun x : ℝ => x ^ D)
  (𝓝 0)
```

because `‖x ^ D‖ = |x| ^ D`.

For API design, I would provide both:

1. A core theorem accepting `IsLittleO`, since Taylor/Peano and derivative APIs naturally produce little-o statements.
2. A wrapper accepting your epsilon-radius hypothesis, or a bridge lemma converting between them.

If C4 already produces its remainder directly in epsilon-radius form, then your current `hjet` is perfectly reasonable and likely easier to use inside the split proof.

## 2. Separate admissibility constants and signed moments

Separate data \((\rho_i,\kappa_i,\delta_i)\) cause no problem.

Use:

- `ρ := min ρ₁ ρ₂` for a shared global lower envelope;
- separate partition lower bounds
  \[
  Z_i(q)\ge C_{0,i}q;
  \]
- or, if convenient, a shared local package
  \[
  \kappa=\max(\kappa_1,\kappa_2),\qquad
  \delta=\min(\delta_1,\delta_2).
  \]

There is no hidden need for the two potentials to have the same constants.

For moments, define the signed quantity as intended:

```lean
A_s K q := ∫ x ^ s * exp (-(q⁻²) * K x)
```

For estimates, pass to norms:

\[
|x^s|=|x|^s
\]

for natural `s`. Hence

\[
|A_s(K,q)|
\le \int |x|^s e^{-q^{-2}K(x)}\,dx
\le C_{\rho,s}q^{s+1}.
\]

Odd `s` therefore causes no issue. The quotient algebra is ordinary signed real algebra; only its estimates use absolute values.

You will need:

- integrability of `x ^ s * exp (...)`;
- `abs_integral_le_integral_abs` or the corresponding norm-of-integral estimate;
- nonvanishing of both denominators, obtained from
  `0 < C₀ᵢ * q ≤ A_0 Kᵢ q`.

No upper bound on \(A_0\) is needed for the displayed quotient decomposition, although one follows from the global lower envelope.

## 3. Recommended epsilon-of-room ending

I recommend a direct `Metric.tendsto_nhds` proof with explicit eventual estimates. It matches the quantifier structure of `hjet` and avoids forcing an epsilon-dependent majorant into `squeeze_zero_norm'`.

The proof shape is:

```lean
rw [Metric.tendsto_nhds]
intro η hη

-- C is the fixed inner Gaussian constant.
let M : ℝ := max C 1
let εj : ℝ := η / (4 * M)

have hM : 0 < M := by
  dsimp [M]
  positivity

have hεj : 0 < εj := by
  dsimp [εj]
  positivity

rcases hjet εj hεj with ⟨δj, hδj, hjet_local⟩
```

Then establish eventually:

1. the splitting radius lies inside the jet radius;
2. the normalized inner contribution is at most `C * εj`, hence at most `η / 4`;
3. the normalized outer contribution has norm below, say, `η / 2`;
4. all needed positivity and denominator facts hold.

Schematically:

```lean
have hinner :
    ∀ᶠ q in 𝓝[>] 0, ‖innerScaled q‖ ≤ η / 4 := by
  -- use hjet_local and C * εj ≤ η / 4

have houter_tendsto :
    Tendsto outerScaled (𝓝[>] 0) (𝓝 0) := by
  -- superpolynomial Gaussian tail estimate

have houter :
    ∀ᶠ q in 𝓝[>] 0, ‖outerScaled q‖ < η / 2 := by
  have := (Metric.tendsto_nhds.1 houter_tendsto) (η / 2) (by positivity)
  simpa [dist_eq_norm] using this

filter_upwards [hinner, houter, hdecomp] with q hi ho hsplit
rw [hsplit]
calc
  dist (innerScaled q + outerScaled q) 0
      = ‖innerScaled q + outerScaled q‖ := by simp [dist_eq_norm]
  _ ≤ ‖innerScaled q‖ + ‖outerScaled q‖ := norm_add_le _ _
  _ < η := by linarith
```

This is clearer than `squeeze_zero_norm'`: for every target `η`, you first choose the jet epsilon small enough, and only then shrink `q`. That is exactly the quantifier order being proved.

### Radius suggestion

Unless \(q^{4/5}\) is important elsewhere, consider using

\[
r(q)=\sqrt q.
\]

For \(q>0\),

\[
\frac{r(q)^2}{q^2}=\frac1q,
\]

so the outer factor becomes \(e^{-c/q}\), still smaller than every power, while avoiding rational `Real.rpow` bookkeeping. Eventually `sqrt q ≤ δj` is also straightforward. The \(4/5\) choice is mathematically fine, but `sqrt` is likely substantially easier in Lean.

In summary: the C3 estimates are correctly scaled; separate admissibility constants and signed moments are harmless; add exponent side conditions or subtraction-free variants; and use a direct `Metric.tendsto_nhds` epsilon-of-room proof.