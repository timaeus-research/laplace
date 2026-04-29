Short answer: **yes, but not as a fully generic “any `g`” theorem**.  
**Minimum-LOC path = a B/C hybrid**:

1. **Use the quartic transport corollary for piece 1.**
2. **Bundle pieces 2+3 into one odd kernel helper.**
3. **Bundle pieces 4–9 into one exact bulk-error helper** proved by one local/tail split.

I would **not** write 9 lemmas, and I would **not** build the fully generic abstraction you sketched unless you expect to reuse it several more times.

---

## What to do

Define

```lean
def odd5Kernel (u) :=
  Qcφ u * Cψ u + Cφ u * Qψ u

def bulkErr (t : ℝ) (u) :=
  t^2 * φ_conn t u * ψ_rem t u
    - Qcφ u * Qψ u
    - (1 / Real.sqrt t) * odd5Kernel u
```

Then prove the decomposition

```lean
t^2 * ∫ φ_conn t u * ψ_rem t u * gW u * exp (-s_t u) ∂u
  - c_QQ * D_t
=
(∫ Qcφ u * Qψ u * gW u * exp (-s_t u) ∂u - c_QQ * D_t)
+ ∫ ((1 / Real.sqrt t) * odd5Kernel u) * gW u * exp (-s_t u) ∂u
+ ∫ bulkErr t u * gW u * exp (-s_t u) ∂u
```

Then triangle inequality gives 3 terms only.

---

## Why this is the minimum-LOC path

### Don’t do 9 lemmas
You’ll duplicate:
- integrability witnesses,
- local/tail splits,
- `t ≥ 1` bookkeeping,
- powers of `‖u‖`,
- polynomial-growth tail arguments.

That’s the expensive part in Lean, not the actual estimates.

### Don’t do the fully generic “any `g`” theorem
It’s elegant mathematically, but in Lean it usually means:
- more parameters,
- more measurable/integrable assumptions,
- more coercion fights,
- more time spent instantiating than saved.

If this is the **last** major asymptotic lemma in the file, the generic theorem is probably **not** worth it.

---

# The two helpers you actually want

---

## Helper A: odd pieces 2+3 together

Prove something like:

```lean
lemma abs_integral_odd5_scaled_le :
  ∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
    |∫ ((1 / Real.sqrt t) * odd5Kernel u) * gW u * exp (-s_t u) ∂u| ≤ K / t
```

### Why it’s easy
`odd5Kernel` is odd:
- `Qcφ` even, `Cψ` odd  => product odd
- `Cφ` odd, `Qψ` even   => product odd

So

```lean
∫ odd5Kernel * gW = 0
```

and hence

```lean
∫ ((1 / √t) * odd5Kernel) * gW * exp(-s_t)
= (1 / √t) * ∫ odd5Kernel * gW * (exp(-s_t) - 1)
```

Then your Stage-1 corrected-bracket machinery should give an `O(1/√t)` bound for the integral, and the extra `1/√t` prefactor yields `O(1/t)`.

### This is the right abstraction boundary
A single odd-kernel helper is worth it. It’s small and reusable.

---

## Helper B: one bulk bound for pieces 4–9

Prove:

```lean
lemma abs_integral_bulkErr_le :
  ∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
    |∫ bulkErr t u * gW u * exp (-s_t u) ∂u| ≤ K / t
```

This is the real LOC saver.

---

# How to prove `bulkErr` cleanly

## Local region: one triangle inequality covers pieces 4–9

On `‖u‖ ≤ R * √t`, expand by Taylor:

```lean
bulkErr t u
=
(1/t)      * Cφ u * Cψ u
+ t        * Qcφ u * Rψ t u
+ t        * Rφ t u * Qψ u
+ (√t)     * Cφ u * Rψ t u
+ (√t)     * Rφ t u * Cψ u
+ t^2      * Rφ t u * Rψ t u
```

Then one pointwise estimate:

```lean
|bulkErr t u| ≤ (K / t) * (1 + ‖u‖^8)
```

for `t ≥ 1`.

That works because:

- piece 4: `(1/t) * |Cφ Cψ| ≤ K/t * (1 + ‖u‖^6)`
- pieces 5,6: `t * |Q * R| ≤ K/t * (1 + ‖u‖^8)`
- pieces 7,8: `√t * |C * R| ≤ K/t^(3/2) * (1 + ‖u‖^7) ≤ K/t * (1 + ‖u‖^8)` since `t ≥ 1`
- piece 9: local bound gives at worst `K/t^2 * ‖u‖^8 ≤ K/t * (1 + ‖u‖^8)` for `t ≥ 1`

So yes: **pieces 4–9 really can be handled by one triangle inequality** on the local region.

---

## Tail region: do **not** use `Rφ`, `Rψ`

This is the key point.

Because the remainder bounds are only local, the tail proof should **not** mention `Rφ` or `Rψ` at all.

Instead, on the tail set `R * √t ≤ ‖u‖`, use the **exact definition**:

```lean
bulkErr t u =
t^2 * φ_conn t u * ψ_rem t u
  - Qcφ u * Qψ u
  - (1 / √t) * odd5Kernel u
```

Then bound each exact term by polynomial growth.

Also use the tail relation

```lean
√t ≤ ‖u‖ / R,   t ≤ ‖u‖^2 / R^2,   t^2 ≤ ‖u‖^4 / R^4
```

So any bad positive power of `t` can be traded for extra powers of `‖u‖`.

That gives a tail bound of the form

```lean
|bulkErr t u| ≤ K * (1 + ‖u‖^M)
```

on the tail set, uniformly in `t`.

Then your existing tail-indicator Gaussian machinery gives the needed `≤ K/t` after integration.

### This is why a combined helper is better than termwise `Q*R`, `C*R`
If you try to prove separate global lemmas for pieces 5–8, you’ll keep re-encoding
“local = use Taylor remainder, tail = unfold exact definition and use growth”.
That’s where the LOC explodes.

---

# So: can one sharp helper handle pieces 5–8?

**Yes — but make it a helper for the combined exact bulk error, not for explicit `Q*R` / `C*R` pieces.**

That’s the important design choice.

If you insist on separate helpers for `Q*R`, `C*R`, you’ll pay the tail cost four times.

---

# Recommended proof order

This is the order I’d implement:

### 1. Define the kernels
- `odd5Kernel`
- `bulkErr`

### 2. Prove kernel facts
- `odd5Kernel_odd`
- `abs_odd5Kernel_le : |odd5Kernel u| ≤ K * (1 + ‖u‖^5)`

### 3. Prove the odd integral helper
- parity rewrite
- corrected bracket bound
- conclude `K/t`

### 4. Prove local pointwise bound for `bulkErr`
```lean
‖u‖ ≤ R*√t -> |bulkErr t u| ≤ (K/t) * (1 + ‖u‖^8)
```

### 5. Prove tail pointwise bound for `bulkErr`
using exact definition + growth + `R*√t ≤ ‖u‖`

### 6. Prove the integrated `bulkErr` bound
split local/tail once

### 7. Final theorem
sum:
- leading quartic transport
- odd helper
- bulk helper

---

# What I would *not* do

## Not A
Nine individual lemmas is almost surely the highest LOC.

## Not full B
A fully generic theorem for arbitrary `g` is too abstract unless you still have multiple similar lemmas left.

## Best choice
A **specialized bulk helper** plus a small **odd helper**.

---

# About Mathlib / existing infra

Pure Mathlib won’t give you a turnkey theorem of the form

> “local polynomial / tail polynomial under your rescaled Gaussianized weight implies `K/t`”

You’ll still need your own local/tail wrapper.

So I’d lean on:
- your existing Gaussian integrability witnesses,
- your existing tail indicator lemmas,
- your existing corrected-bracket pattern.

That is enough.

---

# LOC estimate

My rough guess:

- **odd helper (2+3 together):** ~50–90 LOC
- **bulk helper (4–9 together):** ~120–180 LOC
- **final assembly:** ~30–50 LOC

So call it **~200–320 LOC total**.

By contrast:
- 9 standalone bounds: very plausibly **600+ LOC**

---

# Piece 4 standalone estimate

If you did piece 4 alone and already have:
- cubic polynomial bounds,
- integrability of `‖u‖^6 * gW * exp(-s_t)`,
- easy measurability,

then maybe **30–50 LOC**.

If you need to split local/tail manually: **60–90 LOC**.

So: not terrible individually, but still not worth doing termwise.

---

# Bottom line

## My opinionated recommendation

**Do this:**
- keep piece 1 as-is via `rescaledIntegral_QcQ_transport`,
- add **one odd helper** for pieces 2+3,
- add **one exact bulk-error helper** for pieces 4–9,
- finish by a 3-term triangle inequality.

That is the **minimum-LOC** route.

If you want, I can sketch the exact Lean statement/proof skeleton for:
1. `bulkErr`,
2. the local/tail pointwise lemmas,
3. the final `calc` block assembling the theorem.