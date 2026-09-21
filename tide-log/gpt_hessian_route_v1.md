### 1. Correctness

**(a) Yes, for the quadratic observable \(K(w)=\frac12 w^\top Pw\).** With \(a=0\), the cubic correction vanishes, and
\[
\operatorname{trASig}(P,P^{-1})=d.
\]
Thus the supplied explicit expectation theorem gives
\[
|2t\langle K\rangle_{V,t}-d|\le C/t,
\qquad
|t\langle K\rangle_{V,t}-d/2|\le C/(2t).
\]
**Distinguish this \(K\) from \(V\):** this specialisation proves the claim for the Hessian quadratic observable, not directly for the full potential \(K=V\).

For the trace identity, use `matCLM_comp_inv hP` pointwise on `Pi.single i 1`, then `simp [trASig]`.

**(b) Yes**, for \(t>0\):
\[
S=t^{-1}H^{-1},\quad tT:S=T:H^{-1},\quad
-\tfrac12 S(tT:S)=-\frac1{2t}H^{-1}(T:H^{-1}).
\]
This is precisely the coefficient of the centred Gibbs mean.

For the displayed valley tensors, assuming the other independent cubic components vanish,
\[
H^{-1}=
\begin{pmatrix}1&p\\p&p^2+a^{-1}\end{pmatrix},
\qquad
T:H^{-1}=(2abp,-2ab),
\]
so \(H^{-1}(T:H^{-1})=(0,-2b)\), giving **\((0,b/t)\)**. Take \(a>0,t>0\); the existing exact expectation formulas establish that this correction equals the actual mean displacement.

### 2. `quadObservable`

A direct sup-norm proof idiom (`open Matrix`):
```lean
have hw (i : ι) : |w i| ≤ ‖w‖ := by
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i
calc
  |∑ i, w i * (P *ᵥ w) i| = |∑ i, ∑ j, w i * P i j * w j| := by
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  _ ≤ ∑ i, ∑ j, |w i * P i j * w j| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
  _ ≤ ∑ i, ∑ j, ‖w‖ * |P i j| * ‖w‖ := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    simpa only [abs_mul] using
      mul_le_mul (mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _))
        (hw j) (abs_nonneg _) (mul_nonneg (norm_nonneg _) (abs_nonneg _))
  _ = (∑ i, ∑ j, |P i j|) * ‖w‖ ^ 2 := by
    simp_rw [show ∀ i j, ‖w‖ * |P i j| * ‖w‖ =
      |P i j| * ‖w‖ ^ 2 from fun i j => by ring]
    simp only [Finset.sum_mul]
```
`mul_le_mul` produces products, not powers: explicitly use `pow_two` or `ring`. Also, `ring` does not automatically rewrite summands under binders; the last step handles that explicitly.

Set \(C=\frac12\sum_{ij}|P_{ij}|\).

- Base: radius `1`, constant `C`, gradient `0`.
- Jet: `qφ := φ`, bound constant `C`, radius `1`, **remainder constant `0`**.
- Tensor: `A := matCLM P`, `Φ := 0`; all tensor remainders vanish.
- Continuity: unfold `quadForm`; `fun_prop`.
- Symmetry: `quadForm_symm_matCLM hP`, with `dot` unfolded.
- `Φ_symm`: **yes, `by intros; simp`**.
- **Required missing field:** `poly_growth : HasPolyGrowth φ`. Choose witnesses `C, 2`, using
  \[
  |\phi(w)|\le C\|w\|^2\le C(1+\|w\|^2).
  \]
- Do not forget `qφ_bound_const_nonneg` and `jet_const_nonneg`.

Only the **remainders after subtracting the quadratic jet** have constant zero; the base linear remainder generally does not.

### 3. Nearby candidates

**Add `ObservableQuinticApprox` for the same quadratic:** its odd-part remainder is identically zero, so this is nearly free and supports `eq:covK`.

The useful closed form, writing \(\Sigma=P^{-1}\), is
\[
t^2\operatorname{Cov}_{V,t}(K,\psi)\longrightarrow
\frac12\operatorname{tr}(A_\psi\Sigma)
-\operatorname{dot}\!\bigl(\Sigma a_\psi,\ T:\Sigma\bigr).
\]
The cubic contribution has **twice** the coefficient appearing in \(t\langle\psi\rangle\). This follows from Gaussian homogeneity/IBP; proving the corresponding `cov2Coefficient` simplification is a separate algebraic task.

Especially clean corollary:
\[
t^2\operatorname{Var}_{V,t}(K)\longrightarrow d/2.
\]

**Vote: A, plus the cheap quadratic quintic package; add closed-form `eq:covK` if time permits.**