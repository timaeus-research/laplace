Use `set sl := √lam` for Issue 1, and `congrArg (fun x => √t * x)` for Issue 2. I would not use `linear_combination` for either.

## Issue 1

If you already have `set A := cubicScale lam alpha`, this works:

```lean
have h_alpha : -alpha / (2 * lam ^ 2) = -(3 * A / Real.sqrt lam) := by
  unfold_let A
  unfold cubicScale
  set sl : ℝ := Real.sqrt lam with hsl_def
  have hsl2 : sl ^ 2 = lam := by
    rw [hsl_def]
    exact Real.sq_sqrt hlam.le
  have hsl_ne : sl ≠ 0 := by
    rw [hsl_def]
    exact (Real.sqrt_pos.mpr hlam).ne'
  rw [← hsl2]
  field_simp [hsl_ne]
  ring
```

If you prefer not to use `A`, same proof with `cubicScale` directly:

```lean
have h_alpha : -alpha / (2 * lam ^ 2) = -(3 * cubicScale lam alpha / Real.sqrt lam) := by
  unfold cubicScale
  set sl : ℝ := Real.sqrt lam with hsl_def
  have hsl2 : sl ^ 2 = lam := by
    rw [hsl_def]
    exact Real.sq_sqrt hlam.le
  have hsl_ne : sl ≠ 0 := by
    rw [hsl_def]
    exact (Real.sqrt_pos.mpr hlam).ne'
  rw [← hsl2]
  field_simp [hsl_ne]
  ring
```

---

## Issue 2

First turn the Stein identity into the `A,B` form if needed:

```lean
have h_stein' :
    J_n lam alpha gamma 1 t
      + 3 * A / Real.sqrt t * J_n lam alpha gamma 2 t
      + 4 * B / t * J_n lam alpha gamma 3 t = 0 := by
  unfold_let A B
  simpa using J_score_identity hlam hgamma hdisc ht_pos
```

Then multiply by `√t` like this:

```lean
have h_scaled :
    Real.sqrt t * J_n lam alpha gamma 1 t
      + 3 * A * J_n lam alpha gamma 2 t
      + 4 * B / Real.sqrt t * J_n lam alpha gamma 3 t = 0 := by
  have hsqrt_t_ne : Real.sqrt t ≠ 0 := hsqrt_t_pos.ne'
  have htsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht_pos.le
  have htmp := congrArg (fun x : ℝ => Real.sqrt t * x) h_stein'
  simp only [mul_add, mul_zero] at htmp
  rw [show Real.sqrt t * (3 * A / Real.sqrt t * J_n lam alpha gamma 2 t) =
        3 * A * J_n lam alpha gamma 2 t by
        field_simp [hsqrt_t_ne]] at htmp
  rw [show Real.sqrt t * (4 * B / t * J_n lam alpha gamma 3 t) =
        4 * B / Real.sqrt t * J_n lam alpha gamma 3 t by
        rw [← htsq]
        field_simp [hsqrt_t_ne]
        ring] at htmp
  simpa [mul_assoc] using htmp
```

And then the form you actually want:

```lean
have h_key :
    Real.sqrt t * J_n lam alpha gamma 1 t + 3 * A * J_n lam alpha gamma 0 t =
    3 * A * (J_n lam alpha gamma 0 t - J_n lam alpha gamma 2 t) -
      4 * B / Real.sqrt t * J_n lam alpha gamma 3 t := by
  have h_scaled' :
      Real.sqrt t * J_n lam alpha gamma 1 t =
        -3 * A * J_n lam alpha gamma 2 t
          - 4 * B / Real.sqrt t * J_n lam alpha gamma 3 t := by
    linarith [h_scaled]
  rw [h_scaled']
  ring
```

That should slot directly into your current proof.