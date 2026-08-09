## 1. Candidate A

Yes, Candidate A is mathematically correct, including the edge case `m = 0`.

A few implementation details are worth fixing in the statement/proof:

- The radius type and inequalities should follow the actual type used by `HasFPowerSeriesOnBall`—in current analytic APIs this may involve `ℝ≥0∞`/`ENNReal.ofReal`.
- Because membership in the convergence ball is strict, choose a real `ρ > 0` strictly below the available radius and then set, for example,
  ```lean
  u₁ := ρ / 4
  ```
  Thus `‖x‖ ≤ 2 * u₁` implies `‖x‖ ≤ ρ / 2 < ρ`.
- There is no need independently to choose `ρ < min r p.radius`: `HasFPowerSeriesOnBall` already records that its ball radius is within `p.radius`. Choose `ρ < r`, then derive `ρ < p.radius`.

The geometric-tail proof is likely the lightest robust Mathlib proof.

### Coefficient bound

The relevant API name to try first is:

```lean
FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius
```

It is intended to provide boundedness of

```lean
fun k => ‖p k‖ * ρ ^ k
```

when `ρ` is strictly below `p.radius`. Exact coercions around `ρ` depend on whether you keep it as `ℝ`, `ℝ≥0`, or `ℝ≥0∞`.

If its signature is inconvenient, the equally good fallback is the summability lemma around the same API, usually named along the lines of

```lean
FormalMultilinearSeries.summable_norm_mul_pow
```

and then obtain a uniform bound because a summable real sequence is bounded. In practice, the dedicated `norm_mul_pow_le_of_lt_radius` lemma is preferable if it elaborates cleanly.

### Expansion at a point

The projection is indeed:

```lean
HasFPowerSeriesOnBall.hasSum
```

For a series centered at zero, it yields, after simplification, essentially

```lean
HasSum (fun k => (p k) (fun _ => x)) (g x)
```

provided `x` lies in the relevant ball. Depending on the exact signature, the input is either:

- the displacement `x` with `‖x‖ < r`, giving the value at `0 + x`, or
- the point `x` with a proof that it belongs to the ball around `0`.

In either case, `simpa` should remove `0 + x` and `x - 0`.

### Splitting off the first `m + 1` terms

A convenient generic summability lemma is:

```lean
Summable.sum_add_tsum_nat_add
```

It expresses a `tsum` as a finite initial sum plus the shifted tail. Applied with `m + 1`, the finite sum simplifies to the single `m`th term because all terms below `m` vanish.

Alternatively, prove directly that

```lean
g x - P x = ∑' n, (p (n + (m + 1))) (fun _ => x)
```

and bound that shifted `tsum`.

### Bounding each multilinear term

Use the operator-norm estimate:

```lean
ContinuousMultilinearMap.le_opNorm
```

schematically:

```lean
‖(p k) (fun _ => x)‖ ≤ ‖p k‖ * ∏ _ : Fin k, ‖x‖
```

and simplify the finite product to `‖x‖ ^ k`.

Since the codomain is `ℝ`, finish absolute-value goals with:

```lean
Real.norm_eq_abs
```

### Bounding the tail

There does not appear to be a substantially simpler specialized `FormalMultilinearSeries` tail estimate that exactly returns the desired pointwise bound. The standard generic ingredients are:

- `norm_tsum_le` for passing the norm through a `tsum`;
- `tsum_geometric_of_norm_lt_one` or
  `hasSum_geometric_of_norm_lt_one`;
- standard `tsum` lemmas for constants, multiplication, and shifted sequences.

With `q := ‖x‖ / ρ ≤ 1/2`, one gets

```text
∑ k ≥ m+1, C₀ q^k
  = C₀ q^(m+1) / (1-q)
  ≤ 2 C₀ q^(m+1).
```

Thus one can take

```text
C = 2 C₀ / ρ^(m+1).
```

A Lean-friendly variant is to reindex immediately by `k = n + (m + 1)` and factor out `q^(m+1)`, leaving the ordinary geometric series `∑' n, q^n`.

## 2. Continuity and homogeneity of `P`

Let

```lean
def P (x : ι → ℝ) : ℝ := (p m) (fun _ => x)
```

### Continuity

The straightforward proof is composition with the diagonal map:

```lean
have hdiag : Continuous (fun x : ι → ℝ => fun _ : Fin m => x) :=
  continuous_pi fun _ => continuous_id

have hP : Continuous P :=
  (p m).continuous.comp hdiag
```

Depending on elaboration, this often works directly:

```lean
exact (p m).continuous.comp (continuous_pi fun _ => continuous_id)
```

No finite-dimensional argument is needed beyond whatever instances are already required to make `ι → ℝ` a normed space.

### Homogeneity

Yes, the relevant lemma is:

```lean
ContinuousMultilinearMap.map_smul_univ
```

A typical proof is:

```lean
have hhom (c : ℝ) (x : ι → ℝ) :
    P (c • x) = c ^ m * P x := by
  simpa [P, smul_eq_mul] using
    (p m).map_smul_univ c (fun _ : Fin m => x)
```

The exact argument order may differ slightly, but `map_smul_univ` is the correct API. It produces `c ^ m • ...`; in codomain `ℝ`, `simp [smul_eq_mul]` turns this into multiplication.

In fact, the identity holds for all `c`, so the later theorem's weaker assumption `0 ≤ c` is immediate.

## 3. Direct analytic Taylor-remainder theorem?

I would not plan around finding a turnkey theorem of the precise form

```lean
g x - partialSum m x = O(‖x‖^(m+1))
```

in the `HasFPowerSeriesOnBall` API.

Mathlib has:

- general Taylor theorems for sufficiently differentiable functions;
- asymptotic lemmas used to derive derivatives from power-series expansions;
- summability and convergence-radius lemmas for `FormalMultilinearSeries`.

But converting to the general Taylor API would require identifying the coefficients with iterated derivatives and establishing a local derivative bound. That is likely heavier than bounding the power-series tail directly.

There may be `isLittleO`/`isBigO` lemmas for low-order truncations in the analytic implementation, but even if one is available, turning a local `IsBigO` statement into the exact closed-ball inequality and arranging the partial sum to collapse to the `m`th term will still require comparable plumbing. The geometric proof has the advantages that it:

- works directly from `HasFPowerSeriesOnBall`;
- gives an explicit constant;
- handles all `m`, including `m = 0`;
- does not introduce derivatives or factorial conventions.

So Candidate A is the right foundational lemma.

## 4. Vote

**Implement A as a standalone reusable theorem, and put the composed corollary C in the same file.**

That gives the best minimal target:

1. `analytic_remainder_bound` — Candidate A;
2. small helper facts for continuity and homogeneity of the diagonal coefficient;
3. `analytic_laplace_lower_bound` — the composed corollary invoking the already-proved turnkey theorem.

Keeping A as a separate theorem is important: its proof will contain nearly all the difficult analytic and `tsum` work, while C should then be a short interface-validation theorem. Including C in the same development immediately detects mismatches involving:

- `|·|` versus `‖·‖`;
- the factor `2 * u₁`;
- continuity of `P`;
- scalar homogeneity;
- radius coercions;
- the exact quantifier order expected by the Laplace theorem.

So the practical target is **A + C, with A separately named rather than inlined into C**.