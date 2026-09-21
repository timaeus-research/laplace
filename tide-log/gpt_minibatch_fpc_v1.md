## 1. Correctness

**(a–b) Yes, for \(1\le m\le n\), \(n\ge2\):**
\[
\mathbb E_B[\beta(\bar a_B-\bar a,\bar a_B-\bar a)]
=\frac{1-m/n}{m(n-1)}
 \sum_i\beta(a_i-\bar a,a_i-\bar a).
\]
No symmetry of \(\beta\) is required. Thus the note’s sample-covariance convention is consistent, and `minibatchCoeff` should have denominator `m * ((n : ℝ) - 1)`.

**Important correction to the proposed counting statements:** the singleton count requires \(m\ge1\); the pair count as written requires **\(m\ge2\)**. At \(m=1\), Lean’s truncated subtraction makes
```lean
Nat.choose (n - 2) (m - 2) = Nat.choose (n - 2) 0 = 1
```
whereas the pair count is zero. Consequently, your double-sum decomposition using that coefficient also needs \(m\ge2\), or a guarded pair coefficient:
```lean
if 2 ≤ m then Nat.choose (n - 2) (m - 2) else 0
```
The off-diagonal sum is over **ordered** pairs.

For centered `x i`, the key identity is
\[
\sum_{i\ne j}\beta(x_i,x_j)=-\sum_i\beta(x_i,x_i),
\]
since \(\beta(\sum_i x_i,\sum_j x_j)=0\). Singleton and pair inclusion probabilities then give the stated constant.

**(c)** `m = n`: the only batch is `univ`, so the centered mean and covariance vanish. For `n = 1`, necessarily `m = 1`; covariance again vanishes. The usual `n−1` sample covariance is undefined mathematically. Lean’s totalized division makes the displayed expressions zero, so you can extend the formal identity to this case, but document that convention rather than calling it an ordinary sample covariance.

## 2. Lean route

### Sum interchange

For additive commutative monoids, use **natural scalar multiplication**, not multiplication by a real count. Replace the dependent range by an indicator sum, then ordinary `Finset.sum_comm` suffices.

Here is the core idiom, with `P` the batch finset and `hc` the already-proved singleton count:

```lean
-- hc : ∀ i, (P.filter (fun B => i ∈ B)).card = k
have hind (B : Finset (Fin n)) :
    (∑ i ∈ B, f i) = ∑ i : Fin n, if i ∈ B then f i else 0 := by
  have he : Finset.univ.filter (fun i => i ∈ B) = B := by
    ext i
    simp
  rw [← Finset.sum_filter, he]
calc
  (∑ B ∈ P, ∑ i ∈ B, f i)
      = ∑ B ∈ P, ∑ i : Fin n, if i ∈ B then f i else 0 := by
          simp_rw [hind]
  _ = ∑ i : Fin n, ∑ B ∈ P, if i ∈ B then f i else 0 := Finset.sum_comm
  _ = ∑ i : Fin n, k • f i := by
          simp_rw [← Finset.sum_filter, Finset.sum_const, hc]
  _ = k • ∑ i : Fin n, f i := by rw [Finset.smul_sum]
```

Use `classical`. This avoids needing to select a dependent-range interchange lemma. These are proof idioms, not pin-tested snippets.

### Binomial ratios

Prove **natural-number cross-multiplication identities first**, then cast:
\[
m\binom nm=n\binom{n-1}{m-1},
\]
and, for \(m\ge2\),
\[
m(m-1)\binom nm=n(n-1)\binom{n-2}{m-2}.
\]
Obtain the second by applying the first recurrence twice. Reindex to successors locally when applying `Nat.succ_mul_choose_eq` / `Nat.choose_mul_succ_eq`; normalize multiplication order and equality orientation.

Once those natural identities are available, the real-number stage has this shape:

```lean
have hn0 : (n : ℝ) ≠ 0 := by positivity
have hC0 : (Nat.choose n m : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hmn))
have hcast :
    (m : ℝ) * (Nat.choose n m : ℝ) =
      (n : ℝ) * (Nat.choose (n - 1) (m - 1) : ℝ) := by
  exact_mod_cast hrec
apply (div_eq_div_iff hC0 hn0).2
nlinarith [hcast]
```

For the pair ratio, cast subtraction explicitly:
```lean
rw [Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : 1 ≤ m)] at hcast
```
Then `field_simp` and `nlinarith`/`ring` finish. Ensure every division is already typed in `ℝ`.

**Again:** the unguarded second ratio is false at `m = 1`; handle singleton batches separately, or prove the ratio for the guarded count.

**Statement recommendation:** public theorem with ordinary `n m`, hypotheses `1 ≤ m`, `m ≤ n`, `2 ≤ n`. Split `m = 1` internally; use successor-indexed helper lemmas only where convenient. This keeps the API aligned with `FullStep.lean`.

## 3. Bilinear API and instances

Use
```lean
β : V →ₗ[ℝ] V →ₗ[ℝ] W
```
with real-module assumptions. It gives the needed algebra directly:
```lean
(β.map_sum ...)                 -- first argument, equality of linear maps
((β x).map_sum ...)             -- second argument
```
Likewise use `β.map_add`, `(β x).map_add`, and `map_smul`; evaluation or `simp` handles the first-argument linear-map equality. You need not depend on specialized `map_add₂` names. Two explicit linearity hypotheses would duplicate this API.

Instances:

- `fun x y => Matrix.vecMulVec x y`: bilinear; `LinearMap.mk₂` is appropriate.
- **To match the actual seabed**, use
  ```lean
  fun X Y => X * Σ * Yᵀ
  ```
  rather than `X * Σ * Y`. Transpose is real-linear, so this remains bilinear.
- The untransposed formula follows under symmetry of the centered Hessians. Without symmetry, it is not the covariance sandwich appearing in `stateTerm`.
- No positivity assumption on `Σ` is needed for the identity; positivity matters only for subsequent covariance/PSD interpretations.

For the revised nonnegativity proof, derive `1 ≤ n` from `hm` and `hmn`, hence `0 ≤ (n : ℝ) - 1`; the existing numerator argument survives unchanged.

**Vote: A, modified to guard the pair count at `m = 1` and use the transposed matrix sandwich matching `stateTerm`.**