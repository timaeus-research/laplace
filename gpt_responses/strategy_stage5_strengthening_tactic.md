**Short answer:** take **Path A’, not full Path B**: prove a **specialized quintic coordinate-Stein lemma** using your new `gaussian_sixth_moment_formula` + existing 4th-moment formula, then use it to split the target integral into exactly the two helpers you already have:
- `gaussian_linear_cubic`
- `gaussian_quad_quad` with `B := cubicPartialOp T (Hinv b)`.

That is the minimum-LOC route.

---

## Q1. Best path?

### Recommended: **Path A’ = specialized Stein via 6th+4th moments**
You do **not** want to collapse all 15 pairings directly against the `A,b,T` sums in the final theorem. That’s the 1000-LOC trap.

Instead prove the reusable helper:

```lean
private lemma gaussian_quintic_coord_stein
    (k a b c d e : ι)
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∫ u, u k * u a * u b * u c * u d * u e * gaussianWeight H u
      =
        (Hinv k a) * ∫ u, u b * u c * u d * u e * gaussianWeight H u
      + (Hinv k b) * ∫ u, u a * u c * u d * u e * gaussianWeight H u
      + (Hinv k c) * ∫ u, u a * u b * u d * u e * gaussianWeight H u
      + (Hinv k d) * ∫ u, u a * u b * u c * u e * gaussianWeight H u
      + (Hinv k e) * ∫ u, u a * u b * u c * u d * gaussianWeight H u := by
  -- `rw` sixth moment on LHS, fourth moment on each RHS integral, `ring`
```

This is exactly the coordinate-level Stein identity for degree 5 monomials, and it is **cheap** now that you already have the 6th-moment Wick formula.

Then the target theorem is just:
1. expand `quadForm`, `dot`, `T`;
2. apply `gaussian_quintic_coord_stein` termwise;
3. regroup:
   - derivative hits one of the 2 quadratic slots → `gaussian_linear_cubic`
   - derivative hits one of the 3 cubic slots → `gaussian_quad_quad` with `cubicPartialOp`.

So: **Path A is slick, but only after you factor the Wick algebra into the specialized coordinate-Stein helper.**

---

## Q2. 15 pairings → 3 trace classes

Write slots as:

- `A`-slots: `i, j`
- `b`-slot: `k`
- `T`-slots: `l, m, n`

Global scalar prefactor is `(1/2)*(1/6)=1/12`.

### Class I: `k` pairs with an `A` slot
Pairings:
- `(k,i)` or `(k,j)` : 2 choices
- remaining `A` slot pairs with one of `l,m,n` : 3 choices
- last two `T` slots pair together

So multiplicity = **2 * 3 = 6**.

After `A`-symmetry and `T`-symmetry this is one pattern, giving:

```lean
gaussianZ H * (1/2) *
  dot b (Hinv (A (Hinv (tensorContractMatrix T Hinv))))
```

Reason: `6 * (1/12) = 1/2`.

---

### Class II: `k` pairs with a `T` slot, and the remaining pairs are `(i,j)` and `(T,T)`
Choices:
- `k` pairs with one of `l,m,n` : 3 choices
- then forced pairings `(i,j)` and the remaining two `T` slots together

Multiplicity = **3**.

This gives:

```lean
gaussianZ H * (1/4) *
  trASig A Hinv * dot (Hinv b) (tensorContractMatrix T Hinv)
```

Reason: `3 * (1/12) = 1/4`.

---

### Class III: `k` pairs with a `T` slot, and the remaining `A` slots pair crosswise with the remaining `T` slots
Choices:
- `k` pairs with one of `l,m,n` : 3 choices
- the two `A` slots pair with the other two `T` slots: `2! = 2` choices

Multiplicity = **3 * 2 = 6**.

This gives:

```lean
gaussianZ H * (1/2) *
  dot (Hinv b) (tensorContractMatrix T (Hinv.comp (A.comp Hinv)))
```

Reason: `6 * (1/12) = 1/2`.

So after symmetries there are exactly **3** trace patterns, with multiplicities **6, 3, 6**.

---

## Q3. Can coordinate Stein bypass the 6th moment?

**Not really**, unless you already have a genuine Gaussian IBP/Stein theorem in your library.

Without such a theorem, the degree-5 coordinate Stein identity is basically equivalent to the 6th-moment Wick formula plus the 4th-moment Wick formula. So:

- **Yes**, use coordinate-level Stein as the stepping stone.
- **No**, don’t try to prove it from only 4th moments unless you also build a separate IBP theorem.

Given your current infrastructure, the clean route is:

> `gaussian_sixth_moment_formula` + `gaussian_fourth_moment_formula`
> ⇒ `gaussian_quintic_coord_stein`
> ⇒ `gaussian_quad_linear_cubic_explicit`.

That’s the right layering.

---

## Q4. Lean skeleton

Here is the structure I’d use.

### Step 1: specialized coordinate-Stein helper

```lean
private lemma gaussian_quintic_coord_stein
    (k a b c d e : ι)
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∫ u, u k * u a * u b * u c * u d * u e * gaussianWeight H u
      =
        (Hinv k a) * ∫ u, u b * u c * u d * u e * gaussianWeight H u
      + (Hinv k b) * ∫ u, u a * u c * u d * u e * gaussianWeight H u
      + (Hinv k c) * ∫ u, u a * u b * u d * u e * gaussianWeight H u
      + (Hinv k d) * ∫ u, u a * u b * u c * u e * gaussianWeight H u
      + (Hinv k e) * ∫ u, u a * u b * u c * u d * gaussianWeight H u := by
  rw [gaussian_sixth_moment_formula hGauss]
  rw [gaussian_fourth_moment_formula hGauss.toCov4,
      gaussian_fourth_moment_formula hGauss.toCov4,
      gaussian_fourth_moment_formula hGauss.toCov4,
      gaussian_fourth_moment_formula hGauss.toCov4,
      gaussian_fourth_moment_formula hGauss.toCov4]
  ring_nf
```

This should be mostly `rw` + `ring_nf`.

---

### Step 2: main theorem

```lean
private lemma gaussian_quad_linear_cubic_explicit
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (b : ι → ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (hA_symm : ∀ u v, dot u (A v) = dot v (A u))
    (hT_symm : ∀ σ : Equiv.Perm (Fin 3), ∀ v, T (fun i => v (σ i)) = T v)
    (hGauss : LaplaceCov6MomentHypotheses H Hinv) :
    ∫ u : ι → ℝ,
        ((1 / 2 : ℝ) * quadForm A u) * dot b u *
        ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
      = gaussianZ H *
          ((1 / 2 : ℝ) * dot b (Hinv (A (Hinv (tensorContractMatrix T Hinv))))
           + (1 / 4 : ℝ) * trASig A Hinv *
               dot (Hinv b) (tensorContractMatrix T Hinv)
           + (1 / 2 : ℝ) * dot (Hinv b)
               (tensorContractMatrix T (Hinv.comp (A.comp Hinv)))) := by
  classical
  let c : ι → ℝ := Hinv b
  let B : (ι → ℝ) →L[ℝ] (ι → ℝ) := cubicPartialOp T c
  have hB_symm : ∀ u v, dot u (B v) = dot v (B u) :=
    cubicPartialOp_symm (T := T) (c := c) hT_symm

  have hsplit :
      ∫ u,
          ((1 / 2 : ℝ) * quadForm A u) * dot b u *
          ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
        =
      ∫ u,
          (dot (A c) u) * ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
        +
      ∫ u,
          ((1 / 2 : ℝ) * quadForm A u) *
          ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u := by
    -- Expand `quadForm`, `dot`, and the cubic into coordinate sums.
    -- Apply `gaussian_quintic_coord_stein` termwise.
    -- Regroup the 5 derivative-hit terms:
    --   * 2 quadratic hits combine via `hA_symm`
    --   * 3 cubic hits combine via `hT_symm`
    -- Then use:
    --   `quadForm_cubicPartialOp`
    --   `dot_cubicPartialOp`
    --
    -- Tactically:
    --   simp_rw [quadForm, dot]
    --   rw [integral_finset_sum, ...]
    --   simp_rw [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    --   -- inside kernel:
    --   rw [gaussian_quintic_coord_stein ...]
    --   -- collapse the 2 A-hit sums and 3 T-hit sums
    --   ring_nf
    sorry

  calc
    ∫ u,
        ((1 / 2 : ℝ) * quadForm A u) * dot b u *
        ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
      =
        ∫ u, (dot (A c) u) * ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
        +
        ∫ u, ((1 / 2 : ℝ) * quadForm A u) *
             ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u := hsplit
    _ =
      gaussianZ H *
        ((1 / 2 : ℝ) * dot (Hinv (A c)) (tensorContractMatrix T Hinv)
         + (1 / 4 : ℝ) * trASig A Hinv * trASig B Hinv
         + (1 / 2 : ℝ) * trASig (A.comp Hinv) (B.comp Hinv)) := by
      rw [show
            ∫ u, (dot (A c) u) * ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
              =
            (1 / 6 : ℝ) *
              ∫ u, dot (A c) u * T (fun _ => u) * gaussianWeight H u by
            simp [mul_assoc, integral_mul_left]]
      rw [gaussian_linear_cubic (a := A c) (T := T) hT_symm hGauss.toCov4]
      rw [gaussian_quad_quad (A := A) (B := B) hA_symm hB_symm hGauss.toCov4]
      ring
    _ =
      gaussianZ H *
          ((1 / 2 : ℝ) * dot b (Hinv (A (Hinv (tensorContractMatrix T Hinv))))
           + (1 / 4 : ℝ) * trASig A Hinv *
               dot (Hinv b) (tensorContractMatrix T Hinv)
           + (1 / 2 : ℝ) * dot (Hinv b)
               (tensorContractMatrix T (Hinv.comp (A.comp Hinv)))) := by
      simp [c, B, cubicPartialOp_trASig, cubicPartialOp_trASig_compSig]
      -- one separate lemma for the first dot-term rotation
      -- using symmetry of `A` and `Hinv`
      -- then `ring`
      sorry
```

---

If you want, I can also write the **exact five-term regrouping shape** inside `hsplit` so you can line it up with your current coordinate expansions.