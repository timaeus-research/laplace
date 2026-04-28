Overall: the plan is good, but I’d lock in **two changes now**.

## 1. Main architectural adjustment

### Change A: don’t target `t * N_t - Z * m = O(1/t)` first
For the sharp rate, that target forces you to also sharpen the partition asymptote to `D_t - Z = O(1/t)`, because
\[
tE_t - m = \frac{tN_t - Zm}{D_t} + m \frac{Z-D_t}{D_t}.
\]
If `D_t - Z` is only `O(t^{-1/2})`, you lose the sharp rate.

### Better target
Prove instead the **centered numerator estimate**
\[
|t \cdot N_t(\phi\psi) - m \cdot D_t| \le K/t,
\qquad m := \langle a, H^{-1} b\rangle.
\]
Then
\[
tE_t - m = \frac{tN_t - mD_t}{D_t},
\]
so the existing weak denominator lower bound `D_t ≥ Z/2` is enough.

This is the cleanest sharp-track route.

---

## 2. Biggest hidden issue: homogeneity

Your Stage 2 formulas as written are too strong unless the jets are genuinely homogeneous:

- `cV((√t)⁻¹ • u) = cV(u) / t^(3/2)` needs cubic homogeneity.
- `qφ((√t)⁻¹ • u) = qφ(u) / t` needs quadratic homogeneity.

If you only assume:
- `cV` is odd and `|cV w| ≤ C ‖w‖³`,
- `qφ` is even and `|qφ w| ≤ C ‖w‖²`,

then you **cannot** rewrite them as `cV u / √t` and `qφ u / t`.

### Fix
Use the **scaled jets directly**:
- `s₁(t,u) := t * cV ((Real.sqrt t)⁻¹ • u)`
- `qφₜ(u) := qφ ((Real.sqrt t)⁻¹ • u)`

Then you prove:
- `rescaledPerturbation V H t u = s₁(t,u) + r₂(t,u)` with `|r₂| ≤ C ‖u‖⁴ / t`
- `φ((√t)⁻¹ • u) - (√t)⁻¹ * dot a u = qφₜ(u) + r₃(t,u)` with `|r₃| ≤ C ‖u‖³ / t^(3/2)`

This is enough for parity:
- `s₁(t, ·)` is odd,
- `qφₜ` is even.

So **function jets are fine for the bound-only theorem**, provided you formulate the rescaled expansions this way.

---

## 3. Q1/Q2 recommendations

## Q1. Structure shape
Use:

- `PotentialJetApprox ... extends PotentialApprox ...`
- `ObservableJetApprox ... extends ObservableApprox ...`

That is the cleanest choice.

Why:
- sharp proofs still need all weak fields,
- theorem reuse is easy via `hV.toPotentialApprox` / `hφ.toObservableApprox`,
- constructor ergonomics are still fine because you can set `toPotentialApprox := ...`.

I would **not** use sibling structures with duplicated fields.

---

## Q2. Jet encoding
For the current goal, use **function-valued jets**, not tensors:

- `cV : (ι → ℝ) → ℝ` with `Function.Odd cV`
- `qφ : (ι → ℝ) → ℝ` with `Function.Even qφ`

and global bounds
- `|cV w| ≤ C * ‖w‖^3`
- `|qφ w| ≤ C * ‖w‖^2`

This is the right level for the sharp **rate-only** theorem.

### When tensors become worth it
If you later want the explicit second coefficient (`lem:laplace_cov2` style contraction formulas), then yes, you’ll want a stronger layer:
- symmetric trilinear / tensor data for the cubic jet,
- symmetric bilinear / quadratic-form data for the quadratic jets.

But don’t impose that now.

---

## 4. Stress-test of the parity strategy

The parity plan is sound, with two caveats.

### Caveat 1: use centered G1
For the sharp pair estimate, the natural leading piece is not
- `dot a * dot b * gW * (exp(-s_t)-1)`

but
- `(dot a * dot b - m) * gW * (exp(-s_t)-1)`.

That is what matches `tN_t - mD_t`.

Then the linear term is
\[
\int ( \dot a\,\dot b - m)\, s_1(t,u)\, gW(u)\,du,
\]
and this vanishes because:
- `dot a * dot b - m` is even,
- `s₁(t,·)` is odd,
- `gW` is even.

So the parity cancellation is actually cleaner in the centered formulation.

---

### Caveat 2: you still need integrability companions
Yes, you will probably still need companion lemmas or inline integrability proofs for:
- the odd leading term,
- the Taylor remainder term,
- the observable-jet remainder terms.

But this is manageable, and conceptually the same kind of work as in the weak track.

The good news: with global jet bounds `‖·‖³` / `‖·‖²`, every “explicit parity term” is dominated by polynomial times Gaussian, so those integrability proofs are straightforward.

---

## 5. Suggested sharp-track scope

## Recommendation: **bound-only first**
Do **not** try to close the explicit coefficient theorem in the same pass.

Reason:
- rate-only sharp proof works with arbitrary odd/even jet functions plus growth bounds,
- explicit coefficient formulas really want homogeneous/tensor structure,
- mixing both goals will bloat Stage 0 and Stage 2.

So I’d scope the first pass as:

1. jet structures,
2. rescaled local decomposition lemmas,
3. scalar exp-Taylor remainder bound,
4. centered pair-numerator sharp estimate,
5. sharp pair-expectation theorem,
6. final covariance sharp theorem.

Then later:
- a stronger `...TensorJetApprox` or `...HomogeneousJetApprox`,
- explicit coefficient theorem in a follow-on file.

---

## 6. What to lock in now

I would lock these in immediately:

### Lock now
1. **Centered numerator target**
   ```lean
   |t * rescaledNumerator ... (fun w => φ w * ψ w)
      - dot a (Hinv b) * rescaledPartition V t| ≤ K / t
   ```

2. **Scaled-jet formulation**
   - `t * cV ((Real.sqrt t)⁻¹ • u)`
   - `qφ ((Real.sqrt t)⁻¹ • u)`

3. **Function-valued jets with parity + global growth + continuity**

4. **New sharp helpers**, not refactoring the weak helpers into a common abstraction yet.

### Defer
1. tensor encoding,
2. explicit second coefficient,
3. any abstraction trying to unify weak and sharp helpers.

---

## 7. Recommended Lean structure definitions

These match your current style and support the bound-only sharp track well.

```lean
/-- Sharp local approximation package for the potential.

`cV` is an odd cubic-scale jet in the sense needed for the sharp covariance
rate. We do *not* assume exact cubic homogeneity here; for the sharp bound it
is enough to have oddness plus the global `O(‖w‖^3)` bound, and to use the
scaled jet `t * cV ((Real.sqrt t)⁻¹ • u)` in the rescaled formulas. -/
structure PotentialJetApprox
    (V : (ι → ℝ) → ℝ)
    (H : (ι → ℝ) →L[ℝ] (ι → ℝ))
    extends PotentialApprox V H where
  /-- Cubic-scale jet. -/
  cV : (ι → ℝ) → ℝ
  /-- Continuity of the cubic jet. -/
  cV_continuous : Continuous cV
  /-- Oddness of the cubic jet. -/
  cV_odd : Function.Odd cV
  /-- Global cubic-growth constant for the jet. -/
  cV_bound_const : ℝ
  cV_bound_const_nonneg : 0 ≤ cV_bound_const
  /-- Global cubic-growth bound: `|cV w| ≤ C · ‖w‖^3`. -/
  cV_bound : ∀ w : ι → ℝ, |cV w| ≤ cV_bound_const * ‖w‖ ^ 3
  /-- Radius for the quartic local remainder. -/
  jet_radius : ℝ
  /-- Constant for the quartic local remainder. -/
  jet_const : ℝ
  jet_radius_pos : 0 < jet_radius
  jet_const_nonneg : 0 ≤ jet_const
  /-- Local quartic remainder:
  `|V(w) - ((1/2) * quadForm H w + cV w)| ≤ C · ‖w‖^4`
  on the closed ball of radius `jet_radius`. -/
  jet_bound : ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
    |V w - ((1 / 2 : ℝ) * quadForm H w + cV w)| ≤ jet_const * ‖w‖ ^ 4
```

```lean
/-- Sharp local approximation package for an observable.

`qφ` is an even quadratic-scale jet in the sense needed for the sharp
covariance rate. We do *not* assume exact quadratic homogeneity here; for the
sharp bound it is enough to have evenness plus the global `O(‖w‖^2)` bound,
and to use the scaled jet `qφ ((Real.sqrt t)⁻¹ • u)` in the rescaled formulas. -/
structure ObservableJetApprox
    (φ : (ι → ℝ) → ℝ)
    (a : ι → ℝ)
    extends ObservableApprox φ a where
  /-- Quadratic-scale jet. -/
  qφ : (ι → ℝ) → ℝ
  /-- Continuity of the quadratic jet. -/
  qφ_continuous : Continuous qφ
  /-- Evenness of the quadratic jet. -/
  qφ_even : Function.Even qφ
  /-- Global quadratic-growth constant for the jet. -/
  qφ_bound_const : ℝ
  qφ_bound_const_nonneg : 0 ≤ qφ_bound_const
  /-- Global quadratic-growth bound: `|qφ w| ≤ C · ‖w‖^2`. -/
  qφ_bound : ∀ w : ι → ℝ, |qφ w| ≤ qφ_bound_const * ‖w‖ ^ 2
  /-- Radius for the cubic local remainder. -/
  jet_radius : ℝ
  /-- Constant for the cubic local remainder. -/
  jet_const : ℝ
  jet_radius_pos : 0 < jet_radius
  jet_const_nonneg : 0 ≤ jet_const
  /-- Local cubic remainder:
  `|φ(w) - (dot a w + qφ w)| ≤ C · ‖w‖^3`
  on the closed ball of radius `jet_radius`. -/
  jet_bound : ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
    |φ w - (dot a w + qφ w)| ≤ jet_const * ‖w‖ ^ 3
```

Optional tiny helpers you’ll almost certainly want:

```lean
@[simp] lemma PotentialJetApprox.cV_zero
    (hV : PotentialJetApprox V H) : hV.cV 0 = 0 := by
  simpa using hV.cV_odd 0

@[simp] lemma ObservableJetApprox.qφ_zero
    (hφ : ObservableJetApprox φ a) : hφ.qφ 0 = 0 := by
  simpa using hφ.qφ_even 0
```

---

## 8. Minimal revised proof roadmap

I’d revise your stages to:

1. **Jet structures** above.
2. **Rescaled decomposition lemmas** using scaled jets:
   - `rescaledPerturbation = s₁ + r₂`
   - observable rescaled remainder `= q_t + r₃`
3. **Exp remainder lemma**:
   `|exp (-r) - 1 + r| ≤ C * r^2 * exp |r|`
   (don’t get stuck on the exact `1/2` constant).
4. **Centered sharp numerator theorem**
   for `t * rescaledNumerator(φψ) - m * rescaledPartition`.
5. Divide by partition using the **existing weak lower bound**.
6. Combine with existing `O(1/t)` single-observable expectation bound to get sharp covariance.

---

## 9. Consult budget

For bound-only sharp track with the centered-numerator adjustment: probably **about the same or slightly less** than the weak track.

I’d re-consult at:
1. after Stage 2, if the scaled-jet local lemmas get messy;
2. before any attempt at explicit coefficients.

If you want, I can also sketch the exact theorem statements I’d introduce next, especially the centered sharp pair-numerator lemma and the scaled-jet local bounds.