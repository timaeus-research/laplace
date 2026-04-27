Here’s my concrete recommendation.

## Short version

1. **Do not use only**  
   - `V = ½ x'Hx + O(‖x‖³)` and  
   - `φ = a·x + O(‖x‖²)`, `ψ = b·x + O(‖x‖²)`  
   **if you want the sharp `O(t⁻²)` covariance rate.**  
   Those hypotheses are enough for a clean **weaker** rate:
   \[
   \mathrm{Cov}_t[\phi,\psi] = \frac{\langle a, H^{-1} b\rangle}{t} + O(t^{-3/2}),
   \]
   equivalently
   \[
   |\,t\cdot \mathrm{Cov}_t[\phi,\psi] - \langle a,H^{-1}b\rangle\,| \le K/\sqrt t.
   \]

2. If you want the primer’s sharp rate
   \[
   \mathrm{Cov}_t[\phi,\psi] = \frac{\langle a,H^{-1}b\rangle}{t} + O(t^{-2}),
   \]
   then in an **explicit-estimate-only** formalization you should package one more jet:
   - for `V`: an **odd cubic jet** `C₃` plus a quartic remainder,
   - for `φ, ψ`: **even quadratic jets** `Qφ, Qψ` plus cubic remainders.

3. Make the **main theorem explicit-rate style**, same as 1D:
   ```lean
   ∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
     |t * gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / t
   ```
   Then add a short `Tendsto` / `IsBigO` corollary later.

4. For the proof architecture, do **one change-of-variables lemma up front**, then do everything on the rescaled side.  
   Also: **do not** expose `FubiniIBPHypothesis` in Phase 5. Use a derived Gaussian moment lemma instead.

---

# (1) Hypothesis package

## A. Minimal package for a **weaker but robust** theorem

If you want the cleanest inequality-only theorem first, I’d use:

### Potential
- `V 0 = 0`
- local cubic remainder near `0`:
  \[
  |V(w) - \tfrac12\,\mathrm{quadForm}\ H\ w| \le C \|w\|^3
  \]
  on `‖w‖ ≤ R`
- global coercivity:
  \[
  V(w) \ge c \|w\|^2
  \]
  for some `c > 0`

### Observables
For each of `φ`, `ψ`:
- `φ 0 = 0`
- local linear approximation:
  \[
  |\phi(w) - a\cdot w| \le C \|w\|^2
  \]
  on `‖w‖ ≤ R`
- polynomial growth:
  \[
  |\phi(w)| \le K (1 + \|w\|^p)
  \]
  with `p : ℕ`

This is enough for:
```lean
∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
  |t * gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / Real.sqrt t
```

That theorem is genuinely natural and should go through with the machinery you already have plus coercive Gaussian domination.

---

## B. Package for the **sharp primer rate** `O(t⁻²)`

To get
```lean
|t * gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / t
```
without invoking full `ContDiff`, I would strengthen the local hypotheses to include the next jet explicitly.

### Potential: odd cubic jet
Add a function `cV : (ι → ℝ) → ℝ` such that:
- `Function.Odd cV`
- `|cV w| ≤ C * ‖w‖^3`
- local quartic remainder:
  \[
  |V(w) - (\tfrac12\,\mathrm{quadForm}\ H\ w + cV(w))|
    \le C \|w\|^4
  \]
  on `‖w‖ ≤ R`

### Observables: even quadratic jets
For `φ`, choose `qφ`; for `ψ`, choose `qψ`, with:
- `Function.Even qφ`, `Function.Even qψ`
- `|qφ w| ≤ C * ‖w‖^2`, similarly for `qψ`
- local cubic remainder:
  \[
  |\phi(w) - (a\cdot w + qφ(w))| \le C \|w\|^3
  \]
  and similarly for `ψ`

### Why this matters
This is the clean way to formalize the parity cancellations that kill the `t^{-1/2}` correction terms:
- cubic potential term = **odd**
- quadratic observable correction = **even**
- Gaussian weight = **even**

So all offending first corrections integrate to zero by oddness.

Without these jets, you have only absolute bounds, and Lean will not be able to recover the hidden parity cancellation.

---

## C. Growth assumptions: keep them polynomial

I would **not** restrict to `K * (1 + ‖w‖²)` unless you want a very narrow theorem.

Use a reusable predicate like:
```lean
def HasPolyGrowth (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ K : ℝ, ∃ p : ℕ, 0 ≤ K ∧ ∀ w, |f w| ≤ K * (1 + ‖w‖ ^ p)
```

That is enough for all the integrability and tail estimates you need under coercivity.

---

## D. Practical Lean advice: use closed-ball hypotheses

Use `‖w‖ ≤ R`, not `< R`.

That makes the scaling lemmas much easier.

---

# (2) Shape of the conclusion

## Recommendation
Make the **primary theorem** explicit-rate, same style as your 1D theorem:
```lean
∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
  |t * gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / t
```

Then derive a corollary:
```lean
Filter.Tendsto (fun t => t * gibbsCov V t φ ψ) Filter.atTop
  (nhds (dot a (Hinv b)))
```

## Why
- It matches the existing 1D library.
- It avoids filter algebra during the hard proof.
- It gives a usable numerical rate immediately.

## But:
If you only assume the weaker remainder package, then the honest conclusion should be:
```lean
∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
  |t * gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / Real.sqrt t
```

So my strong recommendation is:

- either **state two theorems** (`weak` and `sharp`), or
- if you only want one theorem named `lem:laplace_cov`, use the **sharp jet package**.

---

# (3) Bridge from rescaled to original: the clean Lean design

## Best design
Define a direct rescaled weight:
```lean
rescaledWeightDirect V t u := Real.exp (-(t * V ((Real.sqrt t)⁻¹ • u)))
```

and rescaled numerators:
```lean
rescaledNumerator V t F :=
  ∫ u, F ((Real.sqrt t)⁻¹ • u) * rescaledWeightDirect V t u
```

Then define a rescaled expectation/covariance on the `u`-space.

## Prove exactly one substitution theorem
Prove once:
```lean
gibbsExpectation V t F = rescaledExpectation V t F
gibbsCov V t φ ψ = rescaledCov V t φ ψ
```
for `t > 0`.

After that, **never go back** to the original variable in the asymptotic proof.

## Also prove the pointwise factorization
Using `rescaling_identity`:
```lean
rescaledWeightDirect V t u
  = gaussianWeight H u * Real.exp (-rescaledPerturbation V H t u)
```

## Important implementation point
For **domination**, do **not** globally work with
```lean
gaussianWeight H u * exp (-rescaledPerturbation ...)
```
because `exp(-s_t)` is only controlled locally.

Instead:
- use `rescaledWeightDirect` for global bounds via coercivity,
- use the factorization only on the local region where Taylor estimates apply.

That split will save you a lot of pain.

---

# (4) How to use `gaussian_second_moment_eq_inverse_entry`

Don’t use the scalar coordinate theorem directly in the Phase 5 proof.

First prove this wrapper:

```lean
theorem gaussian_dot_mul_dot
    ...
    (a b : ι → ℝ) :
    ∫ u : ι → ℝ, dot a u * dot b u * gaussianWeight H u
      = gaussianZ H * dot a (Hinv b)
```

This should be your Phase 5 interface to Gaussian moments.

Also prove:

```lean
theorem integral_odd_mul_gaussian_eq_zero
    (hf_odd : Function.Odd f)
    (hf_int : Integrable (fun u => f u * gaussianWeight H u)) :
    ∫ u, f u * gaussianWeight H u = 0
```

Those two lemmas capture essentially all Gaussian input needed for the covariance theorem.

---

# (5) `FubiniIBPHypothesis`: defer it

I would **not** make `lem:laplace_cov` depend on raw `FubiniIBPHypothesis`.

Use one of these:

### Best
Finish `GaussianDecay.lean`, then import it and use the ready-made Gaussian moment theorem.

### If not finished yet
Expose only a compact derived hypothesis, e.g.
```lean
(h_gauss2 :
  ∀ a b, ∫ u, dot a u * dot b u * gaussianWeight H u
    = gaussianZ H * dot a (Hinv b))
```

That keeps Phase 5 focused on Laplace asymptotics, not on replaying Phase 4 plumbing.

---

# (6) File organisation

I’d split into **two files**.

## `Laplace/Multi/RescaledIntegrals.lean`
Put here:
- `dot`
- `rescaledWeightDirect`
- rescaled numerator / expectation / covariance
- change-of-variables bridge
- factorization via `rescaling_identity`
- local rescaled bounds from the jet hypotheses
- coercive domination / tail lemmas
- elementary `exp` remainder inequalities

## `Laplace/Multi/Covariance.lean`
Put here:
- `gaussian_dot_mul_dot`
- odd Gaussian integral vanishing
- partition asymptotics
- single-observable expectation bound
- pair-observable asymptotics
- quotient/covariance algebra
- final `lem:laplace_cov`

If you try to put all of that in one file, I’d expect it to get long and harder to navigate.

---

# (7) First lemmas to state and prove

Here is the order I’d attack.

## 1. The change-of-variables bridge
This is the biggest potential blocker, so do it first.

```lean
theorem gibbsExpectation_eq_rescaledExpectation
    (ht : 0 < t) :
    gibbsExpectation V t F = rescaledExpectation V t F
```

and similarly for covariance.

If Mathlib fights you here, isolate it in a small specialized dilation lemma for `(ι → ℝ)`.

---

## 2. Gaussian bilinear moment contraction
```lean
theorem gaussian_dot_mul_dot
    ...
    (a b : ι → ℝ) :
    ∫ u, dot a u * dot b u * gaussianWeight H u
      = gaussianZ H * dot a (Hinv b)
```

This should be proved once and then reused everywhere.

---

## 3. Odd Gaussian integrals vanish
```lean
theorem integral_odd_mul_gaussian_eq_zero
    (hf_odd : Function.Odd f)
    (hf_int : Integrable (fun u => f u * gaussianWeight H u)) :
    ∫ u, f u * gaussianWeight H u = 0
```

This is essential if you take the sharp jet route.

---

## 4. Rescaled local bounds
Weak version:
```lean
lemma abs_rescaledPerturbation_le
lemma abs_rescaledObservable_linear_error_le
```

Sharp version:
```lean
lemma abs_rescaledPerturbation_sub_cubicJet_le
lemma abs_rescaledObservable_sub_linear_quadJet_le
```

These are the true workhorses.

---

## 5. Scalar `exp` error lemmas
Weak theorem:
```lean
lemma abs_exp_neg_sub_one_le :
  |Real.exp (-r) - 1| ≤ Real.exp |r| * |r|
```

Sharp theorem:
```lean
lemma abs_exp_neg_sub_one_add_le :
  |Real.exp (-r) - (1 - r)| ≤ (|r|^2 / 2) * Real.exp |r|
```

These make the weight expansion manageable.

---

## 6. Asymptotic integral lemmas
These should come before the final covariance theorem.

### Partition
Sharp:
```lean
theorem rescaledPartition_eq_gaussianZ_add_O_inv
```

### Single observable
```lean
theorem rescaledExpectation_linear_observable_O_inv
```

### Pair observable
Weak:
```lean
theorem rescaledPair_eq_main_add_O_inv_three_halves
```

Sharp:
```lean
theorem rescaledPair_eq_main_add_O_inv_sq
```

---

## 7. Final quotient algebra lemma
A purely scalar helper:
```lean
lemma cov_rate_of_num_den_rates
```
Something of the form:
- `D_t = Z + O(1/t)`
- `N_t = A/t + O(1/t^2)`
- `M_t = O(1/t)`
- `N'_t = O(1/t)`
- `Z > 0`
implies
- `N_t / D_t - (M_t / D_t) * (N'_t / D_t) = A / Z / t + O(1/t^2)`.

This avoids repeating denominator algebra in the main proof.

---

# Likely Mathlib friction points

## Biggest
### 1. Dilation change-of-variables on `(ι → ℝ)`
This is the one I’d expect to cost time.

I would **not** plan around `MeasurePreserving`, because scaling is not measure-preserving.  
You want a specialized “integral under scalar dilation” lemma.

If there is already a suitable theorem in your 1D development, reuse the pattern.

---

### 2. Oddness under `u ↦ -u`
This should be much easier than scaling.

Search for things around:
- `MeasurePreserving.neg`
- `map_neg_eq_self`
- integral under negation / additive equivalence

If needed, a direct proof via invariance of Lebesgue measure under the linear isometry `u ↦ -u` is totally reasonable.

---

### 3. Norm choice on `ι → ℝ`
Watch this carefully.

Depending on instances, the default norm on `ι → ℝ` may not be the coordinate Euclidean norm you mentally expect. If this becomes annoying, define your own:
```lean
noncomputable def coordDot (x y : ι → ℝ) := ∑ i, x i * y i
noncomputable def coordNormSq (x : ι → ℝ) := coordDot x x
```
and state the local bounds in terms of that.

This can save a lot of pointless norm-equivalence friction.

---

# My recommended top-level theorem skeleton

## Sharp theorem
```lean
theorem gibbsCov_first_order_rate
    (V φ ψ : (ι → ℝ) → ℝ)
    (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ)
    (hV : PotentialJetApprox V H)
    (hφ : ObservableJetApprox φ a)
    (hψ : ObservableJetApprox ψ b)
    (hGauss : GaussianSecondMomentData H Hinv) :
    ∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
      |t * gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / t
```

## Weak theorem
```lean
theorem gibbsCov_first_order_rate_weak
    ...
    (hV : PotentialApprox V H)
    (hφ : ObservableApprox φ a)
    (hψ : ObservableApprox ψ b)
    ... :
    ∃ K T₀, 1 ≤ T₀ ∧ ∀ t ≥ T₀,
      |t * gibbsCov V t φ ψ - dot a (Hinv b)| ≤ K / Real.sqrt t
```

---

# Bottom line

My strongest recommendation is:

- **Use inequality-based data structures**, not explicit polynomial decompositions, **but**
- if you want the sharp `O(t⁻²)` covariance theorem, include **parity-resolved next jets**:
  - odd cubic jet for `V`,
  - even quadratic jets for `φ, ψ`.

And architect the proof as:

1. one rescaling bridge lemma,
2. all asymptotics on the rescaled side,
3. Gaussian input only through
   - `gaussian_dot_mul_dot`
   - odd Gaussian integral vanishing,
4. final quotient algebra.

If you want, I can next write the actual Lean-style `structure` definitions (`PotentialApprox`, `PotentialJetApprox`, `ObservableApprox`, `ObservableJetApprox`, `HasPolyGrowth`, `dot`) and a concrete dependency graph for the two-file plan.