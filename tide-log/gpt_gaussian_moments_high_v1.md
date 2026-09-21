## 1. Correctness

**Yes: A.1–A.4 are correct**, with unnormalised Lebesgue integrals as written.

- **A.4:** There is no missing \(Z\). Multiplying A.3 by \(P^{-1}_{jl}\) and summing over \(l\) gives
  \[
  \int u_j\prod_s u_{A(s)}g_W
  =\sum_r P^{-1}_{j,A(r)}
       \int\prod_s(\text{if }s=r\text{ then }1\text{ else }u_{A(s)})g_W.
  \]
  Repeated indices are handled correctly: the sum is over **occurrences**, not distinct coordinate values. For \(n=0\), this asserts that the first moment vanishes.

- **Contraction:** Correct:
  \[
  \sum_k(PM)_{lk}M_{A(r),k}
  =((PM)M^\mathsf T)_{l,A(r)}
  =(PP^{-1})_{l,A(r)}
  =\delta_{l,A(r)}.
  \]
  No transpose correction is needed.

- **Exponent Stein:** Correct, including \(c_j=0\). In that case the left side has an odd first-power \(v_j\) factor and integrates to zero; the right side is zero because of its coefficient \(c_j\). Natural subtraction gives exponent zero on the right, harmlessly. **Split this case explicitly** before using a recurrence involving predecessors.

- **Fourth moment:** Exactly the stated seabed pattern:
  \[
  Z(S_{ad}S_{bc}+S_{bd}S_{ac}+S_{cd}S_{ab}),\qquad S=P^{-1}.
  \]

- **Sixth moment:** The correct 15-term expression, grouped by the partner of \(f\), is
  \[
  \begin{aligned}
  Z[&
  S_{af}(S_{bc}S_{de}+S_{bd}S_{ce}+S_{be}S_{cd})\\
  &+S_{bf}(S_{ac}S_{de}+S_{ad}S_{ce}+S_{ae}S_{cd})\\
  &+S_{cf}(S_{ab}S_{de}+S_{ad}S_{be}+S_{ae}S_{bd})\\
  &+S_{df}(S_{ab}S_{ce}+S_{ac}S_{be}+S_{ae}S_{bc})\\
  &+S_{ef}(S_{ab}S_{cd}+S_{ac}S_{bd}+S_{ad}S_{bc})].
  \end{aligned}
  \]
  This agrees with pairing \(f\) first and then applying the quoted fourth-moment pattern, up to commutative rearrangement. The attached material does not include the actual sixth-moment theorem statement, so its precise syntactic ordering remains to be checked.

A.5 is mathematically sound, but field names, argument order, and available `Fin` expansion lemmas require inspecting the package declarations.

## 2. Target and route

**Target the full A package: arbitrary-degree polynomial Stein, both higher hypothesis packages, and their Wick corollaries.** Prefer A over coordinate slicing: the preceding module already supplies essentially all the analytic infrastructure for A.

Recommended implementation order:

1. Exponent-monomial integrability and product integral.
2. One-dimensional recurrence, then exponent Stein.
3. A **finite-subset index Stein lemma**, allowing products over `t : Finset α`.
4. Products of arbitrary linear forms under the standard Gaussian.
5. Whitening, contraction, package adapters, Wick corollaries.

The finite-subset intermediate avoids doing deletion combinatorics directly on `Fin n`.

### Load-bearing idioms

I cannot check the September pin here; the following are API guidance, not a claim of compiled code.

- **Product of sums:** Start with **`Finset.prod_univ_sum`** for the full finite-type identity
  ```lean
  (∏ s, ∑ k, f s k) = ∑ k : Fin n → ι, ∏ s, f s (k s)
  ```
  This avoids manually navigating `piFinset`. Inspect its arguments with `#check`; use `Finset.prod_sum` and the corresponding finite-function indexing only if necessary.

- **Fiberwise product:** Use **`Finset.prod_fiberwise`**, with target index set `Finset.univ`, to establish a reusable lemma:
  ```lean
  (∏ s ∈ t, v (k s)) =
    ∏ i, v i ^ (t.filter (fun s => k s = i)).card
  ```
  Inside each fiber, rewrite `v (k s)` to `v i`; then `Finset.prod_const` supplies the power. Fix the equality orientation once in this helper.

- **Updated exponents:** Prefer splitting off coordinate `j` with **`Finset.mul_prod_erase`**, rather than depending on a specialised update-product lemma:
  \[
  \prod_i v_i^{(\operatorname{update}c\,j\,m)_i}
  =v_j^m\prod_{i\ne j}v_i^{c_i}.
  \]
  On the erased set, `Finset.mem_erase` provides exactly the inequality needed to simplify `Function.update`.

**Expected bottleneck:** converting exponent Stein back to index Stein, especially proving that every removed occurrence in the \(j\)-fiber gives the same exponent vector. Prove that count identity separately. Its core idiom is:

```lean
  classical
  by_cases hij : k r = i
  · -- The filtered erase is the original fiber with r erased.
    -- Rewrite its card with Finset.card_erase_of_mem.
  · -- r is absent from this fiber; erasing it changes nothing.
```

Then regroup the sum over the fiber and use `Finset.sum_const`. Do not let this argument become mixed with integration or whitening.

For C, `integral_prod`/Fubini is only the final step: one must first prove the coordinate-splitting equivalence preserves the relevant product Lebesgue measure. The supplied code gives no reason to pay that additional infrastructure cost.

## 3. Nearby alternatives and cleaner statements

- **Existing Gaussian APIs:** I would briefly search `ProbabilityTheory.IsGaussian`, `gaussianReal`, and `multivariateGaussian` for polynomial Stein or joint Wick identities, but I do **not** know of a ready-made arbitrary mixed fourth/sixth-moment theorem at this pin. Gaussian characteristic-function and covariance infrastructure alone would not shortcut the job: identifying the density, transporting moments, and differentiating sufficiently many times can cost more than A.

- **Cleaner internal generality:** Prove Stein for a family of linear forms:
  \[
  \int (b^\mathsf Tu)\prod_s(a_s^\mathsf Tu)g_W
  =\sum_r(b^\mathsf TP^{-1}a_r)
       \int\prod_{s\ne r}(a_s^\mathsf Tu)g_W.
  \]
  This matches what whitening already forces you to prove. Coordinate Stein is its basis-vector specialisation. I would expose this only if the internal proof makes it cheap.

- **Product representation:** Use `t.erase r` internally; retain “replace factor \(r\) by \(1\)” at the public adapter boundary. Both preserve multiplicities, unlike deleting a coordinate value from the image of `A`.

**Vote: A, modified to use finite-subset/erase products internally and a standard-Gaussian linear-form Stein helper.**