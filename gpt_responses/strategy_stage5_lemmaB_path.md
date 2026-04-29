Short answer: **take Path 2**, but with **one tiny generic rewrite lemma** extracted from the bilinear proof.  
So: **specialize to `FQQ`**, do **not** build full P1, do **not** try Path 3, and I would **not** switch to cross-only.

## My verdict

- **Path 3:** essentially **not viable**.
- **Path 1:** mathematically nice, but **wrong LOC tradeoff right now**.
- **Path 2:** **best minimum-LOC path** for finishing Lemma B.
- **Path 4:** only if you want a checkpoint theorem today, but **not** the shortest route to the full Stage 5 finish.

---

## 1. Is Path 3 viable?

**No, not in the form you want.**

A finite sum of your existing bilinear kernels has the form
\[
\sum_k \big((\alpha_k \cdot u)(\beta_k \cdot u) - m_k\big)
= u^\top M u - c,
\]
so it is always a **quadratic polynomial plus constant**.

But
\[
FQQ(u)=Q_A^c(u)\,Q_B(u)-c_{QQ}
\]
contains the quartic term
\[
\frac14 (u^\top A u)(u^\top B u),
\]
so generically it is **degree 4**, not degree 2.

So there is no decomposition of `FQQ` as a sum of centered bilinear kernels in the original variable `u`, except in degenerate cases.

The only “reduction” is via the lifted variable \(u \otimes u\), where quartics become bilinear, but then your existing theorem no longer applies because:
- the measure is still Gaussian in `u`, not in `u ⊗ u`,
- the perturbation `s_t` is written in `u`,
- all your current infrastructure is for the original ambient space.

So **Path 3 is a dead end for LOC minimization**.

---

## 2. What to do instead?

### Recommended route: **Path 2 + one small generic transport lemma**

The right target is not a generic P1.  
The right target is:

> a lemma saying that an **even centered kernel with a crude polynomial bound** is transported from Gaussian weight to perturbed weight with `O(1/t)` error.

Then instantiate it with
\[
F(u) := Q_A^c(u)\,Q_B(u)-c_{QQ}.
\]

That is much smaller than full P1 because you do **not** abstract over:
- arbitrary growth exponents,
- arbitrary parity modes,
- arbitrary local/tail majorant APIs.

You only need the one kernel you care about, with the one growth estimate you already know it satisfies.

---

## 3. Why Step 1 means Step 2 is “just transport”

Yes — **that is exactly the right mental model**.

Let
\[
K(u):=Q_A^c(u)\,Q_B(u).
\]
If Step 1 proves
\[
\int K(u)\,gW(u)\,du = c_{QQ},
\]
(or `= cQQ * Z`, depending on your normalization), then define
\[
FQQ(u):=K(u)-c_{QQ}.
\]
Then
\[
\int FQQ(u)\,gW(u)\,du = 0.
\]

So the desired asymptotic is just
\[
\int K\,gW\,e^{-s_t}
=
c_{QQ}\,D_t
+
\int FQQ\,gW\,e^{-s_t},
\]
and all the work is to show
\[
\left|\int FQQ\,gW\,e^{-s_t}\right| \le \frac{K}{t}.
\]

So yes: **Step 2 is “transport the centered Gaussian identity across the perturbation.”**

### Cleanest Lean statement

I would state the transport lemma directly in the “already-centered” form:

```lean
lemma abs_integral_centered_QQ_sharp_le
  : ‖∫ u, FQQ u * gW u * Real.exp (-s_t u)‖ ≤ C / t
```

and then a corollary

```lean
lemma integral_QQ_eq_cQQ_mul_Dt_add_error
  : ‖∫ u, KQQ u * gW u * Real.exp (-s_t u) - cQQ * D_t‖ ≤ C / t
```

with `KQQ = QAc * QB` and `FQQ = KQQ - cQQ`.

That keeps the algebra clean.

---

## 4. Minimum-LOC proof plan

Here is the leanest plan I see.

## A. Prove exactly one generic rewrite lemma

You already have the bilinear-specific version. Generalize just the **rewrite**, not the whole bound.

Something like:

```lean
lemma integral_even_centered_eq_corrected_bracket
  (F : E → ℝ)
  (h_even : Function.Even F)
  (h_mean : ∫ u, F u * gW u = 0)
  (h_int_exp : Integrable (fun u => F u * gW u * Real.exp (-s_t u)))
  (h_int_odd : Integrable (fun u => F u * cmm_diag u * gW u)) :
  ∫ u, F u * gW u * Real.exp (-s_t u)
    = ∫ u, F u * gW u * (Real.exp (-s_t u) - 1 + cmm_diag u) := by
```

Why this is cheap:
- subtract the `1` term using `h_mean`,
- kill the `cmm_diag` term using your existing
  `integral_even_mul_cmm_diag_mul_gaussianWeight_eq_zero`.

This should be **much shorter** than the 150 LOC bilinear version if you stop specializing everything to `dot a u * dot b u - m`.

**This is the only generic extraction I would do.**

---

## B. Specialize everything else to `FQQ`

You need only these kernel facts.

### 1. `FQQ` is even
Cheap.

### 2. `∫ FQQ * gW = 0`
This is exactly what your Step 1 gives after rearrangement.

### 3. Growth bound
Prove a crude bound:
\[
|FQQ(u)| \le C(1+\|u\|^4).
\]

That follows from
- `|quadForm A u| ≤ C_A ‖u‖^2`,
- hence `|Q_A^c(u)| ≤ C'_A (1 + ‖u‖^2)`,
- and `|Q_B(u)| ≤ C_B ‖u‖^2`.

Then
\[
|Q_A^c(u)Q_B(u) - c_{QQ}|
\le C(1+\|u\|^4).
\]

This is the key place where specialization saves LOC.

---

## C. Local bound: reuse your existing corrected-bracket local estimate

On the local ball, combine
- your `abs_gaussianWeight_mul_corrected_bracket_local_le`,
- the crude bound `|FQQ(u)| ≤ C(1 + ‖u‖^4)`.

This gives something of the form
\[
|FQQ(u)|\, gW(u)\, |corr_t(u)|
\le \frac{C}{t}(1+\|u\|^N)\,\text{(gaussian majorant)}.
\]

This part should be **short**.

---

## D. Tail bound: do **not** rebuild Glocal/Gtail

This is where I think you can save the most LOC.

Instead of reproducing the full bilinear tail apparatus, do a **crude tail split**.

Write the corrected bracket on the tail as separate terms:
\[
e^{-s_t} - 1 + cmm\_diag.
\]

Then bound the three tail pieces separately:
1. `|FQQ| * gW * exp(-s_t)`
2. `|FQQ| * gW`
3. `|FQQ| * |cmm_diag| * gW`

Now use the indicator trick on the tail set `‖u‖ > R_t`:
\[
1_{\|u\|>R_t} \le \frac{\|u\|^m}{R_t^m}.
\]

Choose one exponent `m` large enough that `R_t^m ≳ t` (and also enough to absorb the `1/√t` if `cmm_diag` carries that). Then every tail term becomes
\[
\le \frac{C}{t}(1+\|u\|^M)\times(\text{integrable weight}),
\]
with:
- Gaussian moments for terms 2 and 3,
- rescaled-weight moments for term 1.

This is **way** cheaper than setting up a new Gtail framework.

### This is the main proof-engineering recommendation.
If your local radius is the usual power `R_t = t^α`, this tail argument is probably **80–150 LOC**, not 400.

---

## 5. Rough LOC estimate

If you follow the above route:

- generic centered-even rewrite: **30–50 LOC**
- `FQQ` even + mean-zero + growth: **50–80 LOC**
- local estimate: **40–70 LOC**
- tail estimate by indicator/moments: **100–150 LOC**
- final combine + transport corollary: **20–40 LOC**

So I think **~250–400 LOC** is realistic.

If you instead build full P1, you are back in the **600+ LOC** zone.

---

## 6. Answer to your “single global majorant?” question

**Probably not worth chasing.**

If your current code only has the corrected-bracket estimate **locally**, then proving a global
\[
gW \cdot |corr_t| \le \frac{C}{t}\,poly(\|u\|)\,\text{gauss}
\]
is likely to cost at least as much as the local/tail split.

Also, in many setups the global `1/t` pointwise bound is not the natural truth on the tail; the `1/t` comes from the **tail indicator** plus Gaussian moments, not from pointwise smallness of the bracket.

So my advice is:

> **Do not try to replace the split with a single global majorant unless that theorem is already almost proved somewhere.**

---

## 7. Should you switch to Path 4?

**No, unless you need a checkpoint deliverable today.**

I would actually expect the **rr / even-centered transport** to be **shorter** than the cross lemma, because:
- you already have the Gaussian constant,
- the kernel is even and centered,
- the odd correction dies by your existing parity lemma.

The cross lemma still needs extracting the leading term, not just transporting a centered mean-zero kernel.

So if your goal is **minimum LOC to meaningful progress**, I would finish **Lemma B Step 2 now**.

---

## 8. Minimal building blocks I’d actually write

If I were doing this, I’d write exactly:

1. `fqq_even`
2. `fqq_gaussian_mean_zero`
3. `abs_fqq_le_const_one_add_norm_pow_four`
4. `integral_even_centered_eq_corrected_bracket`  ← only generic extraction
5. `abs_integrand_fqq_local_le`
6. `abs_integral_fqq_tail_exp_le`
7. `abs_integral_fqq_tail_one_le`
8. `abs_integral_fqq_tail_cmm_le`
9. `abs_integral_centered_QQ_sharp_le`
10. `integral_QQ_eq_cQQ_mul_Dt_add_error`

That’s the minimum-LOC route I’d bet on.

---

If you want, I can next help you sketch the **actual Lean theorem statements** for items 4–10 in a style that should fit mathlib idioms and minimize rewriting pain.