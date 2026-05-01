Short answer: **extract one helper** that bundles

- expanding `dot b u = ∑ l, b l u_l`,
- applying `gaussian_quintic_coord_stein`,
- collapsing `∑ l, b l (Hinv eₓ) l = (Hinv b) x`.

That helper cuts the ugliest part of `hsplit`. Without it, your 600–800 LOC estimate is realistic. With it, I’d expect **~250–400 LOC** for `hsplit`.

## Best structural simplification

I would **not** do the raw 6-index route in `hsplit`. Instead prove:

```lean
private lemma gaussian_dot_quintic_stein
    {H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hGauss : LaplaceCov6MomentHypotheses H Hinv)
    (b : ι → ℝ) (i j p q r : ι) :
    ∫ u : ι → ℝ,
        dot b u * u i * u j * u p * u q * u r * gaussianWeight H u
      =
        (Hinv b) i * (∫ u, u j * u p * u q * u r * gaussianWeight H u)
      + (Hinv b) j * (∫ u, u i * u p * u q * u r * gaussianWeight H u)
      + (Hinv b) p * (∫ u, u i * u j * u q * u r * gaussianWeight H u)
      + (Hinv b) q * (∫ u, u i * u j * u p * u r * gaussianWeight H u)
      + (Hinv b) r * (∫ u, u i * u j * u p * u q * gaussianWeight H u) := by
  classical
  unfold dot
  rw [integral_finset_sum Finset.univ
      (fun l _ => (hGauss.int_6moment l i j p q r).const_mul _)]
  simp_rw [integral_const_mul,
    gaussian_quintic_coord_stein (H := H) (Hinv := Hinv) hGauss]
  repeat' rw [Finset.sum_add_distrib]
  have hcontract : ∀ x : ι,
      ∑ l, b l * (Hinv (stdBasisVec x)) l = (Hinv b) x := by
    intro x
    simpa [stdBasisVec, Pi.single_apply] using
      (Hinv_symm (H := H) (Hinv := Hinv)
        (hGauss := hGauss.toLaplaceCovHypotheses)
        (stdBasisVec x) b).symm
  simp_rw [hcontract]
  ring
```

This helper is **absolutely worth extracting**, even if private and used once.

Once you have it, `hsplit` only needs a **5-fold** expansion, not 6-fold.

---

## 1. Cleanest pointwise expansion recipe

I’d extract two tiny coord-expansion helpers first.

```lean
private lemma half_quad_coord
    (A : (ι → ℝ) →L[ℝ] (ι → ℝ)) (u : ι → ℝ) :
    ((1 / 2 : ℝ) * quadForm A u)
      =
      ∑ i, ∑ j,
        ((1 / 2 : ℝ) * (A (stdBasisVec j)) i) * (u i * u j) := by
  unfold quadForm
  simp_rw [H_apply_eq_sum A u, Finset.mul_sum, Finset.sum_mul]
  ring_nf

private lemma sixth_cubic_coord
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (u : ι → ℝ) :
    ((1 / 6 : ℝ) * T (fun _ => u))
      =
      ∑ p, ∑ q, ∑ r,
        ((1 / 6 : ℝ) * Tcoord T p q r) * (u p * u q * u r) := by
  rw [T_apply_diag_eq_sum]
  ring_nf
```

Then your LHS expansion becomes:

```lean
have h_expand : ∀ u : ι → ℝ,
    ((1 / 2 : ℝ) * quadForm A u) * dot b u *
        ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u
      =
      ∑ i, ∑ j, ∑ p, ∑ q, ∑ r,
        ((1 / 12 : ℝ) * (A (stdBasisVec j)) i * Tcoord T p q r) *
          (dot b u * u i * u j * u p * u q * u r * gaussianWeight H u) := by
  intro u
  rw [half_quad_coord A u, sixth_cubic_coord T u]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  ring_nf
```

### Verdict on step 1
- **Yes**, this is much cleaner than 50 LOC of nested `sum_congr`.
- The idiom is:
  - small expansion helpers,
  - `simp_rw [Finset.mul_sum, Finset.sum_mul]`,
  - one `ring_nf`.

---

## 2. Swapping integral with finite sums

With `gaussian_dot_quintic_stein`, you only swap through **5** sums.

There is no hidden “multi-index integral_fubini for Finset sums” in Mathlib. So yes, it scales linearly with depth.

But the clean pattern is:

1. define one integrability helper
2. do nested `integral_finset_sum`
3. use `simp_rw [integral_const_mul, gaussian_dot_quintic_stein ...]`

Example:

```lean
have hInt : ∀ i j p q r : ι,
    Integrable (fun u : ι → ℝ =>
      ((1 / 12 : ℝ) * (A (stdBasisVec j)) i * Tcoord T p q r) *
        (dot b u * u i * u j * u p * u q * u r * gaussianWeight H u)) := by
  intro i j p q r
  exact (gaussian_dot_quintic_stein (H := H) (Hinv := Hinv) hGauss b i j p q r |>.symm ▸
    (hGauss.int_6moment i j p q r r).const_mul _ ) -- or prove directly by unfolding dot

rw [show (fun u : ι → ℝ =>
      ((1 / 2 : ℝ) * quadForm A u) * dot b u *
        ((1 / 6 : ℝ) * T (fun _ => u)) * gaussianWeight H u)
    = fun u => ∑ i, ∑ j, ∑ p, ∑ q, ∑ r, _ from funext h_expand]

rw [integral_finset_sum Finset.univ (fun i _ => ?_)]
rw [integral_finset_sum Finset.univ (fun j _ => ?_)]
rw [integral_finset_sum Finset.univ (fun p _ => ?_)]
rw [integral_finset_sum Finset.univ (fun q _ => ?_)]
rw [integral_finset_sum Finset.univ (fun r _ => hInt i j p q r)]
simp_rw [integral_const_mul, gaussian_dot_quintic_stein (H := H) (Hinv := Hinv) hGauss b]
```

### Key advice
Avoid `conv_lhs => enter [2, ...]`.  
Instead: prove a per-index rewrite lemma and use `simp_rw`.

---

## 3. Distribute + collect `b_l`

If you use `gaussian_dot_quintic_stein`, this step is mostly gone.

Without the helper, distributing 5 terms across 6 sums is ugly. With the helper, you get a 5-term sum already in `c := Hinv b`.

### If you still need raw distribution

```lean
repeat' rw [Finset.sum_add_distrib]
```

Usually enough after normalizing associativity:

```lean
simp_rw [add_assoc]
repeat' rw [Finset.sum_add_distrib]
```

### Recommendation
Do **not** inline the `∑_l b_l` collapse 5 times. Bundle it into the helper above. That is the single biggest LOC saver.

---

## 4. T-symmetry relabeling: T3 + T4 + T5

Define a 4th-moment abbreviation and symmetry once:

```lean
let M4 : ι → ι → ι → ι → ℝ := fun a b c d =>
  ∫ u : ι → ℝ, u a * u b * u c * u d * gaussianWeight H u

have hM4_perm :
    ∀ σ : Equiv.Perm (Fin 4), ∀ r : Fin 4 → ι,
      M4 (r (σ 0)) (r (σ 1)) (r (σ 2)) (r (σ 3))
        = M4 (r 0) (r 1) (r 2) (r 3) := by
  intro σ r
  unfold M4
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  ring
```

Also define A-coordinate symmetry once:

```lean
have hAcoord_symm : ∀ i j : ι,
    (A (stdBasisVec j)) i = (A (stdBasisVec i)) j := by
  intro i j
  simpa [stdBasisVec, dot, Pi.single_apply, mul_comm, mul_left_comm, mul_assoc] using
    hA_symm (stdBasisVec i) (stdBasisVec j)
```

### Best tactic stack
For each of T3/T4/T5:

- use `rw [Finset.sum_comm]` to move dummy indices into your preferred order,
- use `Tcoord_perm`,
- use `hM4_perm`,
- finish with `ring`.

That’s cleaner than `sum_bij` here.

### Canonical choice
Pick **T5** as canonical:
\[
\sum_{i,j,p,q,k} A_{ij}\, c_k\, T_{pqk}\, M4(i,j,p,q)
\]
Then:
- `T5` is already canonical,
- `T4` needs one swap,
- `T3` needs one cyclic permutation + one `M4` permutation.

So you should **not** do three 50-LOC blocks. With `hM4_perm`, each is closer to 10–20 LOC.

---

## 5. Reverse identification with piece 1 / piece 2

### Piece 1
For T1+T2, the clean path is:

- collapse to a canonical sum involving `(A c) i`,
- then identify that sum with
  \[
  \frac16 \int \dot (A c)\, T(u,u,u)\, gW.
  \]

You want a forward expansion helper for that target, not reverse-engineering the sum.

```lean
have h_expand_piece1 : ∀ u : ι → ℝ,
    (1 / 6 : ℝ) * dot (A c) u * T (fun _ => u) * gaussianWeight H u
      =
      (1 / 6 : ℝ) * ∑ i, ∑ p, ∑ q, ∑ r,
        (A c) i * Tcoord T p q r *
          (u i * u p * u q * u r * gaussianWeight H u) := by
  intro u
  rw [T_apply_diag_eq_sum]
  unfold dot
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  ring_nf
```

Then use:

```lean
have hAc : ∀ i, (A c) i = ∑ j, c j * (A (stdBasisVec j)) i := by
  intro i
  simpa [stdBasisVec] using H_apply_eq_sum A c i
```

### Piece 2
Yes: prove a basis-coordinate lemma for `cubicPartialOp T c`.

```lean
private lemma cubicPartialOp_basis_coord
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => ι → ℝ) ℝ)
    (c : ι → ℝ) (p q : ι) :
    ((cubicPartialOp T c) (stdBasisVec q)) p
      = ∑ k, c k * Tcoord T p q k := by
  -- exactly the same slot-2 multilinearity move as your earlier `hcontract`
  ...
```

Then use a generic quad expansion helper for `B := cubicPartialOp T c`:

```lean
have h_expand_piece2 : ∀ u : ι → ℝ,
    ((1 / 2 : ℝ) * quadForm A u) * ((1 / 2 : ℝ) * quadForm B u) * gaussianWeight H u
      =
      ∑ i, ∑ j, ∑ p, ∑ q,
        ((1 / 4 : ℝ) * (A (stdBasisVec j)) i * (B (stdBasisVec q)) p) *
          (u i * u j * u p * u q * gaussianWeight H u) := by
  intro u
  rw [half_quad_coord A u, half_quad_coord B u]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  ring_nf
```

Then replace `(B (stdBasisVec q)) p` by the `∑ k, c k * Tcoord T p q k` formula and match your canonical T3/T4/T5 sum.

### Verdict on step 5
Yes, the cleanest path is:
- extract `cubicPartialOp_basis_coord`,
- use a reusable `half_quad_coord`,
- identify piece 2 by **forward expansion of the target integral**.

---

## 6. LOC estimate

### If you keep the raw 6-index path
Your **600–800 LOC** estimate is realistic.

### If you extract the right helpers
I’d expect roughly:

- `gaussian_dot_quintic_stein`: 60–100 LOC
- `M4_perm` + `hAcoord_symm`: 20–40 LOC
- `cubicPartialOp_basis_coord`: 30–60 LOC
- `hsplit` main body: 150–250 LOC

So total around **250–400 LOC** for the whole thing.

---

# Specific tactical asks

## a. Concrete snippet: distribute `∑ (a+b+c+d+e)`

```lean
have hsplit5 :
    ∑ i, ∑ j, ∑ p, ∑ q, ∑ r,
      (T1 i j p q r + T2 i j p q r + T3 i j p q r + T4 i j p q r + T5 i j p q r)
    =
      (∑ i, ∑ j, ∑ p, ∑ q, ∑ r, T1 i j p q r)
    + (∑ i, ∑ j, ∑ p, ∑ q, ∑ r, T2 i j p q r)
    + (∑ i, ∑ j, ∑ p, ∑ q, ∑ r, T3 i j p q r)
    + (∑ i, ∑ j, ∑ p, ∑ q, ∑ r, T4 i j p q r)
    + (∑ i, ∑ j, ∑ p, ∑ q, ∑ r, T5 i j p q r) := by
  simp_rw [add_assoc]
  repeat' rw [Finset.sum_add_distrib]
```

That is the idiom I’d use.

---

## b. Recipe: `T1 + T2 = piece1`

Use:

1. `hAcoord_symm`
2. `hM4_perm`
3. `hAc : (A c) i = ∑ j, c j * (A e_j) i`
4. a forward expansion lemma for piece 1.

Sketch:

```lean
-- S1 and S2 from the post-Stein sum
have hS2_eq_S1 : S2 = S1 := by
  -- swap i and j
  rw [show S2 = ∑ j, ∑ i, ... from by rw [Finset.sum_comm]]
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro i _
  -- remaining sums unchanged
  simp_rw [hAcoord_symm i j]
  rw [hM4_perm (Equiv.swap 0 1) (fun
    | 0 => i | 1 => j | 2 => p | 3 => q)] -- or a simpler dedicated swap lemma
  ring

have hS12 :
    S1 + S2
      = (1 / 6 : ℝ) * ∑ i, ∑ p, ∑ q, ∑ r,
          (A c) i * Tcoord T p q r * M4 i p q r := by
  rw [hS2_eq_S1]
  simp_rw [hAc]
  ring
```

Then identify that with piece 1 by your `h_expand_piece1`.

---

## c. Recipe: `T3 + T4 + T5 = piece2`

Use canonical `T5`.

1. prove `T4 = T5` by swapping `q ↔ r` in outer sums and using `Tcoord_perm` + `hM4_perm`.
2. prove `T3 = T5` by cyclic renaming `(p,q,r)` and same symmetry lemmas.
3. then `T3 + T4 + T5 = 3 * T5`.
4. rewrite `3 * (1/12)` to `1/4`.
5. use `cubicPartialOp_basis_coord` to recognize `B`.

Sketch:

```lean
have hT4_eq_T5 : T4 = T5 := by
  -- reorder sums to put the contracted index in the final slot
  repeat' rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro p _
  refine Finset.sum_congr rfl ?_
  intro q _
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Tcoord_perm T hT_symm (Equiv.swap 1 2) (fun
    | 0 => p | 1 => q | 2 => k)]
  -- and M4 symmetry
  ...
  ring
```

Then after `T3 = T5` and `T4 = T5`:

```lean
have hT345 :
    T3 + T4 + T5
      = (1 / 4 : ℝ) * ∑ i, ∑ j, ∑ p, ∑ q, ∑ k,
          (A (stdBasisVec j)) i * c k * Tcoord T p q k * M4 i j p q := by
  rw [hT3_eq_T5, hT4_eq_T5]
  ring
```

Then replace `∑ k, c k * Tcoord T p q k` by `(B (stdBasisVec q)) p` and use `h_expand_piece2`.

---

## d. Worth extracting helper lemmas?

### Definitely yes
I would extract exactly these:

1. **`gaussian_dot_quintic_stein`**  
   This is the big win. It removes the whole `l`-index mess.

2. **`cubicPartialOp_basis_coord`**  
   Makes piece 2 recognition painless.

3. **`M4_perm`**  
   Very cheap, very useful for relabeling.

4. **`half_quad_coord` / `sixth_cubic_coord`**  
   Tiny helpers that make expansions readable.

### Not worth extracting
A giant generic “Stein-after-summing-with-b for arbitrary coefficient tensor” is probably overkill unless you need it again.

---

# Bottom line

## My recommended recipe for `hsplit`

1. Define:
   - `half_quad_coord`
   - `sixth_cubic_coord`
   - `gaussian_dot_quintic_stein`
   - `M4_perm`
   - `cubicPartialOp_basis_coord`

2. Expand LHS only to a **5-fold** sum:
   - expand `Q_A`
   - expand `T`
   - keep `dot b u` intact

3. Swap integral with the 5-fold sum.

4. `simp_rw [integral_const_mul, gaussian_dot_quintic_stein ...]`

5. Split into 5 sums:
   - `repeat' rw [Finset.sum_add_distrib]`

6. Collapse:
   - `T1 + T2` via `A`-symmetry + `H_apply_eq_sum A c`
   - `T3 + T4 + T5` via `Tcoord_perm` + `M4_perm` + `cubicPartialOp_basis_coord`

7. Match each canonical sum with the RHS pieces by forward expansion.

## LOC estimate
- **with helpers**: ~250–400
- **without helpers**: ~600–800

If you want, I can draft the exact Lean skeleton for:

- `gaussian_dot_quintic_stein`
- `cubicPartialOp_basis_coord`
- the canonical `T1/T2` and `T3/T4/T5` collapse blocks.