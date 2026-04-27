Here’s the Lean-aware route I’d recommend.

**(1) Standard idiom for linearity of integrals**

For 2–3 terms, I would **not** use `Finset.sum`; it usually adds more overhead than it removes. The robust pattern is:

```lean
simp_rw [sub_eq_add_neg, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply]
```

This rewrites under lambdas, so `(F - G) a` becomes `F a + - G a`, which matches `integral_add` / `integral_neg`.

Then use a small extensional normalization lemma if needed:

```lean
have hsplit :
    (fun u => f u * ((1 : ℝ) - s u))
      = (fun u => f u) + (fun u => -(f u * s u)) := by
  ext u; ring
rw [hsplit, integral_add hf hg, integral_neg]
```

If unification still resists, `change` is often enough:

```lean
change ∫ u, f u + g u = _   -- before `rw [integral_add ...]`
```

So: **normalize with `simp_rw`, then `change`, then `rw [integral_add, integral_neg, integral_sub]`**.  
`integral_finset_sum` is worth it only if you already have a family `φ : ι → α → ℝ`.

---

**(2) Smarter route: skip generic step 10/11**

Yes: I would **specialize immediately to `n = 0,1,2,3`** and work with the rescaled unnormalized moments

```lean
J_n t := ∫ u, u^n * exp (-u^2 / 2) * exp (-s_t u)
```

Then prove individually:

- `J_0 = M_0 - (B/t) M_4 + O(t⁻¹)`
- `J_1 = -(A/√t) M_4 + O(t⁻¹)`
- `J_2 = M_2 - (B/t) M_6 + O(t⁻¹)`
- `J_3 = -(A/√t) M_6 + O(t⁻¹)`

using your global remainder bound directly.  
This avoids a generic parity framework and most bookkeeping.

Then normalized moments are

```lean
μ_n t = ((Real.sqrt (λ * t))^n)⁻¹ * (J_n t / J_0 t)
```

No need to expand a generic `I_n`.

---

**(3) Avoid `Real.rpow` if possible**

I strongly recommend **not** using `Real.rpow` here. For `n = 0,1,2,3`, write scaling in terms of `Real.sqrt` and integer powers:

```lean
((Real.sqrt (λ * t)) ^ n)⁻¹
```

This is much easier to simplify under assumptions `0 < λ`, `1 ≤ t`. Then use:

- `have ht0 : 0 < λ * t := ...`
- `have hs : 0 ≤ Real.sqrt (λ * t) := Real.sqrt_nonneg _`
- `have hsq : (Real.sqrt (λ * t))^2 = λ * t := by
    nlinarith [Real.sq_sqrt (le_of_lt ht0)]`
  
For the final four moments, parity splitting is overkill; just specialize and simplify.

---

**(4) Final covariance assembly**

Use asymptotic bookkeeping, not `linear_combination`.

Best pattern:

1. Prove
   ```lean
   μ₁ t = c₁ / t + o(t⁻¹)
   μ₂ t = c₂ / t + d₂ / t^2 + o(t⁻²)
   μ₃ t = c₃ / t^2 + o(t⁻²)
   ```
2. Then
   ```lean
   have hprod : μ₂ * μ₁ = (c₂*c₁) / t^2 + o(t⁻²) := ...
   have hcov  : μ₃ - μ₂*μ₁ = (c₃ - c₂*c₁) / t^2 + o(t⁻²) := hμ₃.sub hprod
   ```
3. Finish coefficient arithmetic with a plain
   ```lean
   have hcoeff : c₃ - c₂*c₁ = -2*α/λ^3 := by ring
   simpa [hcoeff]
   ```

So: use `IsLittleO`/`IsBigO` for the asymptotic structure, and only use `ring` for the scalar coefficient identity.

If you want, I can sketch the exact Lean statement shape for the four `J_n` lemmas and the final `μ₁, μ₂, μ₃` pipeline.