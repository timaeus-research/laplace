**Q1 — Order of attack**

Pick **(b)**, but with one shared step first:

1. **Write parity-weight helpers first** (shared by both lemmas).
2. **Finish Lemma B**.
3. **Strengthen `gaussian_quad_linear_cubic` explicitly**.
4. **Finish Lemma A**.

Why: Lemma B does **not** need the strengthened Gaussian 6th-moment formula. So finishing B first validates the whole Stage-5 decomposition/parity/remainder architecture with minimal new algebra. If anything fails, you fail earlier and cheaper. The only common infrastructure worth doing first is the parity-weight package.

---

## Shared infrastructure to add first

I would add **two helpers**, not a public `U_even` API.

### Helper P1: even-centered kernel under perturbed weight
```lean
lemma integral_even_centered_rescaledWeight_O_tinv
  (F : (ι → ℝ) → ℝ) (c : ℝ)
  (h_even : Even F)
  (h_gauss_mean : ∫ u, (F u - c) * gW u = 0)
  (h_poly : |F u - c| ≤ C * (1 + ‖u‖^m)) :
  ∃ K T₀, ... → |∫ u, (F u - c) * gW u * exp (-s_t u)| ≤ K / t
```
Proof: use `∫ (...) gW = 0`, write
`exp(-s_t)-1 = [exp(-s_t)-1 + V₃/√t] - V₃/√t`; the `V₃` term vanishes by parity (`even * odd`), and the bracket is `O(t⁻¹ poly)` from `abs_exp_neg_sub_one_add_le`.

### Helper P2: odd kernel, first correction explicit
```lean
lemma sqrt_t_integral_odd_rescaledWeight_asymptotic
  (F : (ι → ℝ) → ℝ) (c : ℝ)
  (h_odd : Odd F)
  (h_c : c = -(1 / Z) * ∫ u, F u * V₃ u * gW u)
  (h_poly : |F u| ≤ C * (1 + ‖u‖^m)) :
  ∃ K T₀, ... →
    |√t * (∫ u, F u * gW u * exp(-s_t u)) - c * Z| ≤ K / t
```
Then convert `c * Z` to `c * D_t` using your existing/cheap `|D_t - Z| ≤ K/t` (or prove it once using P1 with `F = 1`).

`U_even` should stay **internal** to these proofs.

---

# Q2 — Lemma B plan: concrete sub-task list

Let
- `QQ := Qc_φ * Q_ψ`
- `QC := Qc_φ * C_ψ`
- `CQ := C_φ * Q_ψ`
- etc.

After the exact algebraic decomposition of `t^2 * φ_conn * ψ_rem`, implement these in order:

### 1. Main Gaussian coefficient for `QQ`
Prove:
```lean
lemma gaussian_QcQ_mean
  : ∫ u, (QQ u) * gW u
      = Z * ((1/2) * trASig (A_φ.comp (Hinv.comp (A_ψ.comp Hinv))) 1)
```
Use `gaussian_quad_quad` + `gaussian_quad_expectation`; the `μ_φ` subtraction cancels the disconnected
`(1/4) tr(A_φΣ) tr(A_ψΣ)`.

### 2. Centered even-kernel perturbation lemma for `QQ`
Set
```lean
FQQ u := QQ u - c_QQ
```
Then `FQQ` is even and has zero Gaussian mean by Step 1. Apply **P1**:
```lean
|∫ FQQ * gW * exp(-s_t)| ≤ K/t
```
This is exactly the leading term of Lemma B.

### 3. Odd cross term `QC`
`QC` is odd (`even * odd`). Prove a coarse helper:
```lean
lemma integral_odd_rescaledWeight_O_tminushalf
  (F odd, poly growth) :
  |∫ F * gW * exp(-s_t)| ≤ K / √t
```
(using `∫ F gW = 0` by parity and `abs_exp_neg_sub_one_le`).  
Then
```lean
|(1/√t) * ∫ QC * gW * exp(-s_t)| ≤ K / t
```

### 4. Same for `CQ`
Identical to Step 3.

### 5. Quadratic × remainder: `t * Qc_φ * R_ψ`
New generic helper:
```lean
lemma abs_integral_quad_remainder_le_O_tinv
```
Use `|R_ψ| ≤ C ‖u‖^4 / t^2`, `|Qc_φ| ≤ C(1 + ‖u‖^2)`, so after multiplying by `t` the integrand is
`≤ C (‖u‖^4 + ‖u‖^6) / t`.  
Bound by `integrable_pow_norm_mul_rescaled_weight`.

### 6. Same for `t * R_φ * Q_ψ`
Same helper, swapped roles.

### 7. Cubic × cubic: `(1/t) * C_φ * C_ψ`
Direct moment bound:
`|C_φ C_ψ| ≤ C ‖u‖^6`, hence total `O(1/t)`.

### 8. Cubic × remainder: `√t * C_φ * R_ψ`
Use `|C_φ| ≤ C ‖u‖^3`, `|R_ψ| ≤ C ‖u‖^4 / t^2`, so total
`≤ C ‖u‖^7 / t^(3/2) ≤ C ‖u‖^7 / t`.  
Same for `√t * R_φ * C_ψ`.

### 9. Remainder × remainder: `t^2 * R_φ * R_ψ`
Use the existing sharp-track remainder×remainder helper directly.

### 10. Final assembly
Sum Steps 2–9 with the exact decomposition and absorb constants.

---

## Lemma A plan

1. Prove explicit
```lean
gaussian_quad_linear_cubic_explicit
```
by **one IBP on `(b·u)`**, not by full 15-pairing Wick. Differentiate
`(1/2 Q_A) * (1/6 T)`:
- derivative hitting `Q_A` gives a `linear*cubic` integral → `gaussian_linear_cubic`;
- derivative hitting `T` gives `quad*quad` → `gaussian_quad_quad`.

2. Define `Fodd u := (b·u) * Qc_φ u`.  
Apply **P2** to `Fodd`; the coefficient is exactly the two `T`-contractions **after centering cancels the disconnected trace term**.

3. Define `Feven u := (b·u) * C_φ u`.  
Use **P1** (or plain Gaussian expectation if you compare to `Z` first) with `gaussian_cubic_linear` to get `(1/2)⟨Σb, Φ_φ:Σ⟩`.

4. Bound the remainder term `t√t * (b·u) * R_φ` using your existing cross-linear remainder helper if present; otherwise isolate it as a separate generic bound.

---

## Q4 — sixth moment machinery?

You do **not** need a full `gaussian_sixth_moment_formula`. For the remaining file, the shortest path is the **direct IBP derivation** above. It reuses already-proven `gaussian_linear_cubic` and `gaussian_quad_quad`, and keeps LOC/heartbeats much lower.

---

## Q5 — does centering matter in Lemma A?

It **does matter**.  
You are right that
```lean
∫ μ_φ * (b·u) * gW = 0
```
by parity, so centering does **not** affect the naive Gaussian leading term. But it **does** affect the `-(1/√t) V₃` correction:
```lean
-∫ (b·u) * (Q_φ - μ_φ) * V₃ * gW
```
The `μ_φ` piece is **not zero** because `(b·u) * V₃` is even. It cancels the disconnected trace contribution from `gaussian_quad_linear_cubic_explicit`. So centering is essential for the connected coefficient.

---

## Q6 — heartbeat budget

Yes: expect **1.0M–1.6M** on the parity helpers and possibly **2M+** on the explicit Gaussian IBP lemma if you let `simp/ring_nf` roam. To stay under budget:

- factor algebraic decompositions into tiny lemmas;
- separate pointwise polynomial bounds from integral estimates;
- keep tensor-contraction rewrites out of the final asymptotic lemmas;
- prove the explicit Gaussian formula in 2–3 helper lemmas, not one monolith.

If you want, I can next turn this into a **Lean file skeleton**: theorem names, dependency graph, and the exact order of `have` blocks for Lemma B.