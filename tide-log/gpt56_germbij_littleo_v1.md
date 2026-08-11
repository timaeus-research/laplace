Yes—A is mathematically correct, and using `N : ℕ` is the usual and sufficient formulation of superpolynomial decay.

## 1. Candidate A

A direct Mathlib proof can be written as follows:

```lean
open Filter Asymptotics

theorem lower_bound_not_superpolynomial
    {Δ : ℝ → ℝ} {κ T₀ γ : ℝ}
    (hκ : 0 < κ)
    (hbound : ∀ t, T₀ ≤ t → κ * t ^ γ ≤ Δ t)
    (hdecay : ∀ N : ℕ, Δ =o[atTop] fun t ↦ t ^ (-(N : ℝ))) :
    False := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-γ)

  have hsmall :=
    (hdecay N).def (half_pos hκ)

  have hev :=
    hsmall.and (eventually_ge_atTop (max T₀ 1))

  rcases hev.exists with ⟨t, ht_small, ht⟩

  have ht_one : 1 ≤ t :=
    le_trans (le_max_right T₀ 1) ht
  have ht_pos : 0 < t :=
    lt_of_lt_of_le zero_lt_one ht_one
  have ht_T₀ : T₀ ≤ t :=
    le_trans (le_max_left T₀ 1) ht

  have hNγ : -(N : ℝ) ≤ γ := by
    linarith

  have hpow_le :
      t ^ (-(N : ℝ)) ≤ t ^ γ :=
    Real.rpow_le_rpow_of_exponent_le ht_one hNγ

  have hpow_pos :
      0 < t ^ (-(N : ℝ)) :=
    Real.rpow_pos_of_pos ht_pos _

  have ht_small' :
      |Δ t| ≤ (κ / 2) * t ^ (-(N : ℝ)) := by
    simpa [Real.norm_eq_abs, abs_of_pos hpow_pos] using ht_small

  have hbad :
      κ * t ^ (-(N : ℝ)) ≤
        (κ / 2) * t ^ (-(N : ℝ)) := by
    calc
      κ * t ^ (-(N : ℝ))
          ≤ κ * t ^ γ :=
        mul_le_mul_of_nonnegative_left hpow_le hκ.le
      _ ≤ Δ t :=
        hbound t ht_T₀
      _ ≤ |Δ t| :=
        le_abs_self _
      _ ≤ (κ / 2) * t ^ (-(N : ℝ)) :=
        ht_small'

  have : κ ≤ κ / 2 :=
    (mul_le_mul_right hpow_pos).mp hbad

  linarith
```

The use of `hev.exists` is useful here: one should not rely on `filter_upwards` directly when the target is `False`.

### Why `N : ℕ` is sufficient

The condition

```lean
∀ N : ℕ, Δ =o[atTop] fun t ↦ t ^ (-(N : ℝ))
```

is a standard formalization of “decays faster than every inverse polynomial.” It is enough because, given any real exponent `γ`, Archimedeanness provides a natural `N` with

```text
-N < γ.
```

On `t ≥ 1`, this gives

```text
t ^ (-N) ≤ t ^ γ.
```

Quantifying over all real exponents would be stronger syntactically but adds no useful strength for this contradiction.

In fact, A uses only one such `N`. A slightly more primitive lemma could assume:

```lean
∃ N : ℕ, -(N : ℝ) < γ ∧
  Δ =o[atTop] fun t ↦ t ^ (-(N : ℝ))
```

but the universally quantified version is the more natural public API.

### Edge cases

Neither of the mentioned edge cases breaks the statement:

* `T₀ ≤ 0`: harmless, because the proof works eventually on
  `t ≥ max T₀ 1`.
* `γ ≥ 0`: also harmless. Then the lower bound is constant or growing, which is even more clearly incompatible with superpolynomial decay.

The positivity of `κ` is essential.

---

## 2. Relevant Mathlib names

### Extracting the ε-bound from `IsLittleO`

The convenient API is:

```lean
(hdecay N).def (half_pos hκ)
```

Here the coefficient is inferred as `κ / 2`, and the result is definitionally an eventual estimate of the form

```lean
∀ᶠ t in atTop,
  ‖Δ t‖ ≤ (κ / 2) * ‖t ^ (-(N : ℝ))‖
```

It is preferable to unfolding `IsLittleO` manually. The fully qualified name is:

```lean
Asymptotics.IsLittleO.def
```

### Monotonicity in the exponent

The lighter lemma is:

```lean
Real.rpow_le_rpow_of_exponent_le
```

used as:

```lean
Real.rpow_le_rpow_of_exponent_le ht_one hNγ
```

where:

```lean
ht_one : 1 ≤ t
hNγ    : -(N : ℝ) ≤ γ
```

This avoids explicitly factoring `t ^ γ`.

If the factorization proof is otherwise useful, the relevant facts are:

```lean
Real.one_le_rpow
Real.rpow_add
Real.rpow_pos_of_pos
```

with typical uses:

```lean
Real.one_le_rpow ht_one hexp
Real.rpow_add ht_pos
Real.rpow_pos_of_pos ht_pos x
```

For example:

```lean
have : 1 ≤ t ^ (γ + (N : ℝ)) :=
  Real.one_le_rpow ht_one hexp
```

### Cancelling a positive factor

The clean cancellation step is exactly:

```lean
(mul_le_mul_right hpow_pos).mp hbad
```

where:

```lean
hpow_pos : 0 < t ^ (-(N : ℝ))
```

and:

```lean
hbad :
  κ * t ^ (-(N : ℝ)) ≤
    (κ / 2) * t ^ (-(N : ℝ))
```

---

## 3. Candidate B and the `rpow` rewrite

Because the original threshold `T₀` might be nonpositive, first strengthen it to `max T₀ 1`. Then `t > 0`, which is exactly what `Real.rpow_add` wants.

The relevant identity is:

```lean
t ^ (1 - (m : ℝ) - (d : ℝ) / 2)
  = t * t ^ (-(m : ℝ) - (d : ℝ) / 2)
```

A robust proof is:

```lean
have hrpow :
    t ^ (1 - (m : ℝ) - (d : ℝ) / 2) =
      t * t ^ (-(m : ℝ) - (d : ℝ) / 2) := by
  calc
    t ^ (1 - (m : ℝ) - (d : ℝ) / 2)
        =
        t ^ ((1 : ℝ) + (-(m : ℝ) - (d : ℝ) / 2)) := by
          congr 1
          ring
    _ =
        t ^ (1 : ℝ) *
          t ^ (-(m : ℝ) - (d : ℝ) / 2) := by
          rw [Real.rpow_add ht_pos]
    _ =
        t * t ^ (-(m : ℝ) - (d : ℝ) / 2) := by
          rw [Real.rpow_one]
```

Thus B should look schematically like:

```lean
corollary integral_not_superpolynomial
    -- analytic hypotheses
    (hdecay :
      ∀ N : ℕ,
        Δ =o[Filter.atTop] fun t ↦ t ^ (-(N : ℝ))) :
    False := by
  have hraw :
      ∀ t, T₀ ≤ t →
        κ * (t * t ^ (-(m : ℝ) - (d : ℝ) / 2)) ≤ Δ t :=
    proven_lower_bound -- supplied analytic theorem

  apply lower_bound_not_superpolynomial
      (Δ := Δ)
      (κ := κ)
      (T₀ := max T₀ 1)
      (γ := 1 - (m : ℝ) - (d : ℝ) / 2)
      hκ
      ?_
      hdecay

  intro t ht
  have ht_one : 1 ≤ t :=
    le_trans (le_max_right T₀ 1) ht
  have ht_pos : 0 < t :=
    lt_of_lt_of_le zero_lt_one ht_one
  have ht_T₀ : T₀ ≤ t :=
    le_trans (le_max_left T₀ 1) ht

  have hrpow :
      t ^ (1 - (m : ℝ) - (d : ℝ) / 2) =
        t * t ^ (-(m : ℝ) - (d : ℝ) / 2) := by
    calc
      t ^ (1 - (m : ℝ) - (d : ℝ) / 2)
          =
          t ^ ((1 : ℝ) + (-(m : ℝ) - (d : ℝ) / 2)) := by
            congr 1
            ring
      _ =
          t ^ (1 : ℝ) *
            t ^ (-(m : ℝ) - (d : ℝ) / 2) := by
            rw [Real.rpow_add ht_pos]
      _ =
          t * t ^ (-(m : ℝ) - (d : ℝ) / 2) := by
            rw [Real.rpow_one]

  rw [hrpow]
  exact hraw t ht_T₀
```

The important detail is changing A’s threshold to `max T₀ 1` in B. Otherwise the transformed bound would have to be supplied for potentially nonpositive `t`, where the convenient `rpow_add` theorem is not directly applicable.

---

## 4. Is there a substantially lighter existing API?

The general asymptotics API has lemmas relating `IsLittleO`, `IsBigO`, and related notions, but turning the one-sided ordered lower bound

```lean
κ * t ^ γ ≤ Δ t
```

into the appropriate asymptotic “big omega” statement requires essentially the same positivity and norm bookkeeping. It is unlikely to be shorter or clearer here.

Likewise, APIs for rapidly decreasing functions or Schwartz maps usually package much stronger structure and are not a natural fit for an arbitrary function `Δ : ℝ → ℝ`.

The one clear simplification over the proposed proof plan is:

```lean
Real.rpow_le_rpow_of_exponent_le
```

instead of manually using `Real.rpow_add` and `Real.one_le_rpow` inside A.

## Vote

Put A and B in the same file:

1. A as a small general asymptotic/order lemma, ideally near other auxiliary asymptotics results.
2. B immediately after the analytic lower-bound theorem as its contradiction corollary.

A is reusable and independent of the integral construction; B should contain only the threshold strengthening and the `rpow` normalization.