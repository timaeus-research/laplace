### 1. Replacements A and B

#### A: `linarith [h_half_le]`

Mathematically, yes: `h_half_le` alone is enough.

In Lean, I would write this as:

```lean
linarith only [h_half_le]
```

not

```lean
linarith [h_half_le]
```

because `linarith [h_half_le]` still scans and uses the whole local context; `only` is the important compile-time guard.

For this goal over `ℝ`, current `linarith` should normalize the `/ 2` placement and monomial associativity/commutativity well enough here, so no explicit bridge should be needed. The fact that one side is written

```lean
c * Rφ ^ 2 / 2 * t
```

and the hypothesis has

```lean
c / 2 * (Rφ ^ 2 * t)
```

should not be a problem for current Mathlib’s arithmetic normalization.

That said, if you want a completely tactic-normalizer-independent replacement, this is the robust proof:

```lean
calc
  c / 2 * ‖u‖ ^ 2 + c * Rφ ^ 2 / 2 * t
      ≤ c / 2 * ‖u‖ ^ 2 + c / 2 * ‖u‖ ^ 2 := by
        exact add_le_add_left
          (by
            calc
              c * Rφ ^ 2 / 2 * t = c / 2 * (Rφ ^ 2 * t) := by ring
              _ ≤ c / 2 * ‖u‖ ^ 2 := h_half_le)
          (c / 2 * ‖u‖ ^ 2)
  _ = c * ‖u‖ ^ 2 := by ring
```

If `ring` ever objects because of division normalization, replace those two `by ring`s with `by ring_nf`.

Verdict: **A is sound**, but use `linarith only [h_half_le]`, not bare `linarith [h_half_le]`.

---

#### B: `le_mul_of_one_le_right`

Yes, this is the right lemma/name in current Mathlib. I would add explicit arguments to make elaboration deterministic:

```lean
exact le_mul_of_one_le_right
  (a := ‖u‖ ^ k) (b := ‖u‖)
  (pow_nonneg (norm_nonneg u) k) hu.le
```

So after

```lean
rw [pow_succ]
```

this should close

```lean
‖u‖ ^ k ≤ ‖u‖ ^ k * ‖u‖
```

The relevant shape is:

```lean
le_mul_of_one_le_right :
  0 ≤ a → 1 ≤ b → a ≤ a * b
```

over ordered semirings/ordered rings, so it unifies over `ℝ`.

If somehow the rewrite gives the other multiplication order,

```lean
‖u‖ ^ k ≤ ‖u‖ * ‖u‖ ^ k
```

then use the left variant:

```lean
exact le_mul_of_one_le_left
  (a := ‖u‖ ^ k) (b := ‖u‖)
  (pow_nonneg (norm_nonneg u) k) hu.le
```

Fallback without relying on the convenience lemma:

```lean
calc
  ‖u‖ ^ k = ‖u‖ ^ k * 1 := by rw [mul_one]
  _ ≤ ‖u‖ ^ k * ‖u‖ :=
    mul_le_mul_of_nonneg_left hu.le (pow_nonneg (norm_nonneg u) k)
```

Verdict: **B is sound as written**, with optional explicit `(a := ...) (b := ...)` annotations recommended.

---

### 2. Is targeting `nlinarith` the right compile-time move?

Yes. If 5 `nlinarith`s account for ~22s of a ~36s file, this is clearly the highest-impact target.

The biggest concrete point: use `only`.

```lean
nlinarith [h]
```

uses the full local context plus `h`.

```lean
nlinarith only [h]
```

uses only `h` plus the negated goal.

For deep proofs with huge contexts, this often changes runtime by orders of magnitude. Even if you keep `nlinarith`, try:

```lean
nlinarith only [h_half_le]
```

for A as a minimal diff. It should be vastly cheaper than the old call because it avoids generating degree-2 products from the whole context.

Other advice:

* `maxHeartbeats` does not speed things up; it only changes when Lean gives up.
* Splitting the file may improve incremental rebuilds and parallelism, but it will not fix a single slow tactic inside one declaration. It is secondary here.
* The 54 `positivity` calls are probably not worth touching unless re-profiling after the `nlinarith` fixes shows them becoming dominant.
* If a future `positivity` call is hot, replace it with explicit facts like `sq_nonneg`, `pow_nonneg`, `mul_nonneg`, `div_nonneg`, etc.
* For arithmetic tactics in large contexts, prefer `linarith only [...]`, `nlinarith only [...]`, and small `calc` proofs over broad-context tactic calls.

---

### 3. Replacement for `show t ≤ t ^ 2 by nlinarith`, given `ht : 1 ≤ t`

Clean term-mode replacement:

```lean
show t ≤ t ^ 2
simpa [pow_two] using
  (le_mul_of_one_le_right
    (a := t) (b := t)
    ((zero_le_one : (0 : ℝ) ≤ 1).trans ht)
    ht)
```

If the type of `t` is already forced, the annotation on `zero_le_one` may be unnecessary:

```lean
simpa [pow_two] using
  (le_mul_of_one_le_right (a := t) (b := t)
    (zero_le_one.trans ht) ht)
```

Is replacing a 0.5s `nlinarith` worth it? Not crucial, but the replacement is short, clearer, and removes another nonlinear arithmetic search. I would change it while you are already touching these proofs.