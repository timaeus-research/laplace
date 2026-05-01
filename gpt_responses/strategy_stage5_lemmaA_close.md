Here’s the tactical version I’d implement.

## Q1. Explicit `gaussian_quad_linear_cubic`: yes, do the 1-step IBP; don’t do full Wick

Your IBP plan is the right one. I would **not** go back to coordinate-level sextic expansion unless the operator construction becomes impossible. The clean route is:

### Step 1: prove the uncentered explicit formula
Let
- `Σ := Hinv`
- `cT := tensorContractMatrix T Σ`

Prove something of the form
```lean
private lemma gaussian_quad_linear_cubic_explicit
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (b : ι → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    ...
    :
    ∫ u,
        ((1 / 2 : ℝ) * quadForm A u) * dot b u *
          ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
      =
      gaussianZ H *
        ( (1 / 2 : ℝ) * dot b (Σ (A (Σ cT)))
        + (1 / 4 : ℝ) * trASig A Σ * dot (Σ b) cT
        + (1 / 2 : ℝ) * dot (Σ b)
            (tensorContractMatrix T (Σ.comp (A.comp Σ))) )
```

This comes exactly from your two IBP pieces:

- piece 1:
  ```lean
  (1/6) ∫ dot (A (Σ b)) u * T(u,u,u) * gW
  ```
  handled by `gaussian_linear_cubic`.

- piece 2:
  ```lean
  (1/4) ∫ quadForm A u * T(u,u,Σ b) * gW
  ```
  handled by `gaussian_quad_quad` after introducing the quadratic operator
  `Bc` with
  ```lean
  quadForm Bc u = T(u,u,Σ b).
  ```

### Step 2: immediately derive the centered corollary
This is the one you’ll actually use in Lemma A:

```lean
private lemma gaussian_centeredQuad_linear_cubic_explicit
    ...
    :
    ∫ u,
        (((1 / 2 : ℝ) * quadForm A u) - ((1 / 2 : ℝ) * trASig A Σ)) *
          dot b u * ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
      =
      gaussianZ H *
        ( (1 / 2 : ℝ) * dot b (Σ (A (Σ cT)))
        + (1 / 2 : ℝ) * dot (Σ b)
            (tensorContractMatrix T (Σ.comp (A.comp Σ))) )
```

The centering kills exactly the middle
```lean
(1/4) trASig A Σ * dot (Σ b) cT
```
term, because
```lean
∫ dot b u * ((1/6) * T(u,u,u)) * gW
  = gaussianZ H * ((1/2) * dot (Σ b) cT).
```

That cancellation is the whole reason centering matters here.

### Should you avoid constructing `B'`?
My advice: **no**. Build a small local helper for the partial quadratic operator. A coordinate proof is likely longer and uglier.

I’d do a very local definition, not a giant reusable abstraction:

```lean
private def cubicPartialOp
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (c : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) := ...
```

and then prove only the 3 facts you need:

1. `quadForm (cubicPartialOp T c) u = T (fun | 0 => u | 1 => u | 2 => c)`
2. symmetry of `cubicPartialOp T c`
3. the two contraction identities:
   ```lean
   trASig (cubicPartialOp T c) Σ = dot c (tensorContractMatrix T Σ)
   trASig (A.comp Σ) ((cubicPartialOp T c).comp Σ)
     = dot c (tensorContractMatrix T (Σ.comp (A.comp Σ)))
   ```

That should be materially shorter than direct coordinate summation.

### LOC estimate for Q1
- partial operator + its lemmas: **120–220 LOC**
- explicit uncentered lemma: **80–140 LOC**
- centered corollary: **30–60 LOC**

So **~250–400 LOC** total for the Gaussian helper package is realistic.

---

## Q2. For Lemma A: same B/C hybrid, but do the odd split **under the integral**

The linear/cubic structure does **not** break the bundling pattern. The clean decomposition is:

Let
- `FQ(u) := dot b u * Qφc u` where `Qφc = Qφ - μφ`
- `FC(u) := dot b u * Cφ u`
- `FR_t(u) := t * sqrt t * dot b u * Rφ_t u`

Then after inserting the pointwise observable expansion,
```lean
I_t = ∫ (FC + sqrt t * FQ + FR_t) * gW * exp(-pert_t)
```

Now do **two algebraic splits**:

### Even block
```lean
∫ FC * exp(-pert_t)
  = ∫ FC + ∫ FC * (exp(-pert_t) - 1)
```
Main term: explicit Gaussian integral.
Correction: `O(1/t)` because `FC` is even and the `-V₃/√t` term is odd, so its Gaussian integral vanishes.

### Odd block
Do **not** force a pointwise identity. Use parity after integration:
```lean
∫ sqrt t * FQ * exp(-pert_t)
  = ∫ sqrt t * FQ * (exp(-pert_t) - 1)
```
since `∫ FQ * gW = 0`.

Then split
```lean
sqrt t * (exp(-pert_t) - 1)
  = -V₃ + [sqrt t * (exp(-pert_t) - 1) + V₃]
```
so
```lean
∫ sqrt t * FQ * exp(-pert_t)
  = - ∫ FQ * V₃ * gW
    + ∫ FQ * [sqrt t * (exp(-pert_t) - 1) + V₃] * gW
```

This is the key exact identity at the integral level. It is cleaner than a pointwise split.

- `- ∫ FQ * V₃ * gW`: main constant, handled by the centered Gaussian lemma above.
- bundled remainder:
  ```lean
  Kodd_t(u) := FQ(u) * (sqrt t * (exp(-pert_t u) - 1) + V₃(u))
  ```
  and this is `O(1/t)` after parity/local-tail, exactly as in Lemma B.

Why it still works: the dangerous `t^{-1/2}` part of the bracket is **even** in `u`, and `FQ` is odd, so that contribution is odd and integrates to zero. First nonzero contribution is `O(1/t)`.

So: **same hybrid plan**, just lighter algebra.

---

## Q3. Centering: only the `Qφc` block needs it, but it really is essential there

Yes: the centering issue is localized, but crucial.

If you use raw `Qφ` instead of `Qφc`, then in the odd block’s main cross term you get
```lean
∫ (b·u) * μφ * V₃(u) * gW
```
and this is **not zero**. That produces exactly the unwanted trace term.

What happens mechanically:

- uncentered `gaussian_quad_linear_cubic_explicit` gives **three** terms;
- subtracting `μφ = (1/2) trASig A Σ` times `gaussian_linear_cubic` kills the trace-product term;
- the remaining two terms are exactly the two `A/T` constants in your theorem.

So centering is needed **only** on `Qφc` in the odd block. It does **not** propagate to the `Cφ` block or to the bulk remainder, except that you should consistently use the already-centered pointwise expansion.

In practice: prove and invoke the **centered Gaussian lemma** directly, instead of handling `μφ` separately inside Lemma A.

---

## Q4. LOC estimate

I think **400–600 is optimistic / slightly low**.

My realistic estimate:

- Gaussian helper package for Q1: **250–400 LOC**
- one small linear-linear Gaussian helper if absent: **20–50 LOC**
- Lemma A body, reusing B infrastructure:
  - even split + main term: **80–120 LOC**
  - odd split + explicit centered main term: **120–180 LOC**
  - bundled odd remainder bound: **120–200 LOC**
  - bulk remainder: **100–180 LOC**
  - final algebra / constants / `ring_nf`: **60–120 LOC**

So I’d budget **600–900 LOC total**.

If `cubicPartialOp` or an equivalent contraction-to-operator helper already exists, you might land around **500–700**. Without it, I would not plan on under 600.

---

## Recommended implementation order

1. Add `gaussian_linear_linear` if missing.
2. Define local `cubicPartialOp T c`.
3. Prove its `quadForm`, symmetry, and trace/contraction lemmas.
4. Prove uncentered `gaussian_quad_linear_cubic_explicit`.
5. Prove centered corollary.
6. In Lemma A:
   - substitute the observable expansion,
   - do the **even split** and the **odd-under-the-integral split**,
   - discharge the two Gaussian main terms,
   - bound `Kodd_t`,
   - bound the quartic remainder block,
   - replace `gaussianZ H` by `rescaledPartition V t` using the same partition asymptotic already used in Lemma B.

If you want, I can also sketch the exact Lean `calc` skeleton for the odd block decomposition; that’s the part most likely to save you time.