Use **fresh variables for the square roots, then rewrite `lam` and `t` as squares before `field_simp`**.  
`linear_combination` / `polyrith` are the wrong tools here; this is a single rational identity, not a linear combination of hypotheses.

```lean
have hbridge :
    t^2 * ((Z * IL3 - IL2 * IL1) / Z^2)
      = Real.sqrt t * (J0 * J3 - J2 * J1) / (lam * Real.sqrt lam * J0^2) := by
  rw [hZ_sub, hIL1_sub, hIL2_sub, hIL3_sub, hsqrt_lamt_split]

  -- freeze the square roots
  set sl : ℝ := Real.sqrt lam
  set st : ℝ := Real.sqrt t

  have hsl2 : sl^2 = lam := by
    dsimp [sl]
    nlinarith [hsqrt_lam_sq]
  have hst2 : st^2 = t := by
    dsimp [st]
    nlinarith [hsqrt_t_sq]

  have hlam_ne : lam ≠ 0 := by
    intro h; simpa [h] using hlamt
  have ht_ne : t ≠ 0 := by
    intro h; simpa [h] using hlamt
  have hsl_ne : sl ≠ 0 := by
    intro h
    apply hlam_ne
    rw [← hsl2, h]
    norm_num
  have hst_ne : st ≠ 0 := by
    intro h
    apply ht_ne
    rw [← hst2, h]
    norm_num

  -- crucial step: eliminate lam,t in favour of sl^2, st^2
  rw [← hsl2, ← hst2]

  -- normalize powers/products before clearing denominators
  simp [pow_two, pow_succ, mul_assoc, mul_left_comm, mul_comm,
        div_eq_mul_inv] 

  -- now it is a rational identity in sl, st, J0..J3
  field_simp [hJ0_ne, hsl_ne, hst_ne]
  ring
```

### Why this works
After `rw [← hsl2, ← hst2]`, there are **no sqrt axioms left**: everything is in the polynomial variables `sl, st`. Then `field_simp` turns the goal into a genuine polynomial identity, and `ring` closes it.

### If the goal is still too big
Do it in two smaller lemmas:
1. Show the left side equals  
   `st * (J0*J3 - J2*J1) / (sl^3 * J0^2)`.
2. Then `simpa [sl, st, hsl2, pow_succ, pow_two, mul_assoc, mul_comm]`
   using `show ... = Real.sqrt t * ... / (lam * Real.sqrt lam * J0^2)`.

So: **introduce `sl st`, rewrite `lam,t` as squares, then `field_simp; ring`**.