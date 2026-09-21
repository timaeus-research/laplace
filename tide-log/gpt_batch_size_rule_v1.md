## 1. Mathematics

**A–D are correct with explicit positivity assumptions and two wording corrections.** Require `t > 0`, `λmax > 0`, `d > 0`, `h > 0`, `h pmax < 2`, `pmax = t λmax`, and the stated integer batch/population conditions.

- **A:** Yes. For a uniformly sampled size-`m` subset without replacement, the batch-mean covariance is
  \[
  C_g=\frac1m\left(1-\frac mn\right)S^2,
  \]
  with `S²` normalised by `n−1`. Both covariances are PSD, and taking traces gives the claimed identity.

- **B:** The substitution is exact. But **only the expression retaining `(1−m/n)` is the lower endpoint**. The note’s expression *without* that factor is not generally a lower bound: at `m=n`, the excess is zero, while the note’s expression can be positive. Describe the note’s expression as an approximation when both `m/n` and `h pmax` are small.

- **C:** Correct and sufficient for `ε > 0`. Drop the finite-population factor using `0 ≤ 1−m/n ≤ 1`, then rearrange the upper bound with positive denominators. The resulting threshold can exceed `n`, making the sufficient condition infeasible—not false. In particular, it misses the exact zero-noise case `m=n`.

- **D:** Correct as a sufficient condition. Writing `T = tr C_g`, its constraint is equivalent to
  \[
  h(t^2T+d\varepsilon t\lambda_{\max})\le 2d\varepsilon.
  \]
  For fixed **`T > 0`**, fixed Hessian, dimension and tolerance, the maximal allowed step scales as `t⁻²`; smaller steps also work. Necessity of `h = O(t⁻²)` for bounded excess follows from the **lower bound**, not from the sufficient condition alone. If `T=0`, no such noise-driven restriction exists.

  Yes: under that scaling, `h pmax = O(t⁻¹) → 0`, so the ULA **discretisation inflation** vanishes. The minibatch excess itself need not vanish under `h ∼ c/t²`.

## 2. Lean

The proposed route is sound.

- For PSD scalar multiplication, supply an explicit `0 ≤ c`; over `ℝ`, the ordered-star instances should be routine. Exact lemma names/argument order depend on the checkout.
- Prove scalar nonnegativity separately, especially `1 − (m : ℝ)/(n : ℝ) ≥ 0`.
- Beware natural subtraction and casts in `(n−1)`: establish denominator positivity from `2 ≤ n`, and use `Nat.cast_sub` when necessary.
- `trace_smul` gives the covariance trace identity directly once the matrix identity is available; `trace_sum` is useful for expanding the sample covariance, not essential here.
- C/D reduce to real inequalities using positive denominators and `div_le_iff₀`/`le_div_iff₀`. C needs `tr S² ≥ 0`; **no inverse-monotonicity theorem is needed**—drop the finite-population factor and clear denominators.

## 3. Scope

A+B+C+D is a coherent tide; ~150 lines is plausible if the existing bounds are easy to instantiate. Skip the numerical instances without their missing covariance data.

Defer monotonicity extras: the **bound expressions**, not automatically the actual excess, are linear in `t` at fixed relative step and fixed remaining inputs. Their batch dependence is exactly `1/m−1/n`, only approximately `1/m`.

The four candidates close the intended rule-of-thumb argument without adding avoidable scope.

Vote: A+B+C+D