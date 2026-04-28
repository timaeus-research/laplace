Short answer:

- **For (A)/(C): use Path 2 (IBP)**. It is much cleaner in Lean than a full 4th-moment Wick expansion.
- **For (B): use the 4th-moment direct path**.
- The key is to introduce a **coordinate tensor** once and prove a small library of helper lemmas.

## 1. Helpers I’d define first

Let
```lean
def e (i : ι) : ι → ℝ := Pi.single i 1

def Tcoord (T) (i j k : ι) : ℝ :=
  T ![e i, e j, e k]

def contractVec (T) (Σ : Matrix ι ι ℝ) (l : ι) : ℝ :=
  ∑ j, ∑ k, Tcoord T l j k * Σ j k
```

Then prove these 3 helpers.

### (i) Expansion of `T(u,u,u)`
Do **not** use the `r : Fin 3 → ι` form from `map_sum` in the main proof. Prove a triple-sum lemma once:
```lean
lemma T_apply_diag_eq_sum (u : ι → ℝ) :
  T (fun _ : Fin 3 => u)
    = ∑ i, ∑ j, ∑ k, u i * u j * u k * Tcoord T i j k := by
  -- use `eq_sum_stdBasis u`
  -- substitute in each slot
  -- then `simp` with multilinearity / `Fin.sum_univ_three`
```
This is the right normalization for all later contractions.

### (ii) Coordinate symmetry from `T_symm`
Don’t store extra structure; derive:
```lean
lemma Tcoord_perm (σ : Equiv.Perm (Fin 3)) (r : Fin 3 → ι) :
    Tcoord T (r (σ 0)) (r (σ 1)) (r (σ 2))
      = Tcoord T (r 0) (r 1) (r 2) := by
  simpa [Tcoord, e] using T_symm σ (fun n => e (r n))
```
Then get the two needed corollaries by choosing `r := ![i,j,k]`:
- `Tcoord T i l k = Tcoord T l i k`
- `Tcoord T i j l = Tcoord T l i j` (via a cycle or swap `(0 2)`)

This is much less fiddly than specializing `T_symm` ad hoc every time.

### (iii) Linear factor rewritten through `H`
Prove once:
```lean
lemma dot_eq_sum_H (a u) :
  dotProduct a u = ∑ l, (Hinv a) l * (H u) l := by
  -- use symmetry of Hinv and H ∘ Hinv = id
```
This is the bridge from `(a·u)` to the cubic-IBP lemma.

---

## 2. Proof skeleton for `gaussian_linear_cubic`

Prove first the fixed-`l` contraction:
```lean
have h_l : ∀ l,
  ∫ u, (H u l) * T (fun _ : Fin 3 => u) * gW u
    = Z * (3 * contractVec T Σ l) := by
```

For fixed `l`:

1. Rewrite `T(...)` by `T_apply_diag_eq_sum`.
2. Move sums/constants outside the integral:
   ```lean
   simp_rw [integral_finset_sum, integral_const_mul, Finset.mul_sum, Finset.sum_mul]
   ```
3. Each term is
   ```lean
   ∫ u, (H u l) * (u i * u j * u k) * gW u
   ```
   reorder by `ring_nf`/`ring` to match your cubic IBP lemma:
   ```lean
   ∫ u, u i * u j * u k * (H u l) * gW u
   ```
4. Apply `gaussian_ibp_cubic_f`.
5. Then integrate the resulting quadratic terms using your 2nd-moment lemma:
   - `δ_{li}` term gives `Z * Σ j k`
   - `δ_{lj}` term gives `Z * Σ i k`
   - `δ_{lk}` term gives `Z * Σ i j`
6. After summing over indices you get three sums:
   ```lean
   ∑ j k, Tcoord T l j k * Σ j k
   ∑ i k, Tcoord T i l k * Σ i k
   ∑ i j, Tcoord T i j l * Σ i j
   ```
   Rewrite the last two to the first using `Tcoord_perm`; for the third, use also `Σ` symmetry if you swap the last two indices.

That yields `Z * (3 * contractVec T Σ l)`.

Now finish the main theorem:
```lean
calc
  ∫ u, (dotProduct a u) * T (fun _ => u) * gW u
      = ∑ l, (Hinv a) l * ∫ u, (H u l) * T (fun _ => u) * gW u := by
          rw [dot_eq_sum_H]
          -- move sum outside integral
  _ = ∑ l, (Hinv a) l * (Z * (3 * contractVec T Σ l)) := by simp [h_l]
  _ = Z * 3 * dotProduct (Hinv a) (contractVec T Σ) := by
        simp [contractVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc,
              mul_left_comm, mul_comm]
```

That gives (A).  
For **(C)**, just commute the scalar factors and insert the `1/6`.

---

## 3. For `gaussian_quad_quad`

Yes: do it by 4th moment.

Write
```lean
(½ uᵀAu)(½ uᵀBu)
 = 1/4 * ∑ i j k l, A i j * B k l * u i * u j * u k * u l
```
Then termwise apply `gaussian_fourth_moment_formula`.

Organize the three Wick pairings into helper lemmas:

- pairing 1:
  ```lean
  ∑ i j k l, A i j * B k l * Σ i j * Σ k l
    = tr (A ⬝ Σ) * tr (B ⬝ Σ)
  ```
- pairing 2:
  ```lean
  ∑ i j k l, A i j * B k l * Σ i k * Σ j l
    = tr (A ⬝ Σ ⬝ B ⬝ Σ)
  ```
- pairing 3: same as pairing 2 after renaming / symmetry (`B`, `Σ` symmetric).

So you get
```lean
Z * (1/4 * tr(AΣ) * tr(BΣ) + 1/2 * tr(AΣBΣ))
```

If you want, I can write the exact helper lemmas (`T_apply_diag_eq_sum`, `Tcoord_perm`, and the fixed-`l` IBP lemma) in Lean-ish syntax next.