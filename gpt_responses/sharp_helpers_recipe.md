Yes — your Stage 3 plan is sound. My tactical recommendation:

## Q1. Helper 1: best Lean structure

### (a) Yes: extract the parity lemma

Make it standalone. Suggested statement:

```lean
private lemma integral_centered_bilinear_scaledCubic_eq_zero
    (V : (ι → ℝ) → ℝ) (H Hinv : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (a b : ι → ℝ) [Nonempty ι]
    (hV : PotentialJetApprox V H)
    (hGauss : LaplaceCovHypotheses H Hinv)
    {t : ℝ} (ht : 0 < t) :
    ∫ u : ι → ℝ,
      (dot a u * dot b u - dot a (Hinv b)) *
      (t * hV.cV ((Real.sqrt t)⁻¹ • u)) *
      gaussianWeight H u = 0 := by
  ...
```

Proof pattern:
- `B u := dot a u * dot b u - m` is **even**.
- `C u := t * hV.cV ((Real.sqrt t)⁻¹ • u)` is **odd**.
- So `fun u => B u * C u` is odd.
- Apply `integral_odd_mul_gaussian_eq_zero`.
- For integrability, use
  `|B u| ≤ K₁ * (1 + ‖u‖^2)` and
  `|C u| ≤ K₂ * ‖u‖^3 / Real.sqrt t ≤ K₂ * ‖u‖^3` for `t ≥ 1`
  (or just prove at fixed `t` with denominator left in). Then dominate by Gaussian moments of orders `3,5`.

This lemma will pay for itself.

---

### (b) Main decomposition: use the **corrected bracket**
Do **not** go via
`(exp(-s)-1) = -s + remainder`
as the top-level split.

Instead rewrite the whole integral as

```text
I(t) = ∫ B · gW · (exp(-s_t) - 1 + c_t)
```

where `c_t(u) := t * cV((√t)⁻¹ • u)`.

Why this is best:
- `∫ B · gW = 0`
- `∫ B · c_t · gW = 0`
- so only the corrected bracket remains.

Then use the pointwise identity

```text
exp(-s_t) - 1 + c_t
  = (exp(-s_t) - (1 - s_t)) + (c_t - s_t).
```

So helper 1 reduces to bounding two pieces:
1. Taylor remainder: `|exp(-s_t) - (1 - s_t)|`
2. quartic remainder: `|s_t - c_t|`

That is the cleanest Lean split.

---

### (c) Local/tail handling

#### Local: yes, use the weak-track `Glocal` template
Pick a **small fixed** radius `ρ > 0`, not the full `jet_radius`.
On `‖u‖ ≤ ρ √t`:
- weak bound gives `|s_t(u)| ≤ C₃ ‖u‖^3 / √t ≤ C₃ ρ ‖u‖^2`
- choose `ρ` small enough so `gW(u) * exp |s_t(u)|` is still dominated by `exp(-κ‖u‖²)`.

Then:
- Stage 1 gives `|exp(-s)- (1-s)| ≤ s² exp|s|`
- hence local Taylor term is `≤ const * ‖u‖^6 / t * exp(-κ‖u‖²)`
- Stage 2 gives `|s_t - c_t| ≤ const * ‖u‖^4 / t`
- multiplied by `|B| ≤ const*(1+‖u‖²)`, both are Gaussian-integrable and yield `K/t`.

#### Tail: simpler than weak helper 1
You do **not** need a fancy bound on `gW * |exp(-s)-1|`.

Use the crude bound
```text
|exp(-s_t) - 1 + c_t| ≤ exp(-s_t) + 1 + |c_t|.
```

So tail integrand is dominated by sums of:
- `|B| * gaussianWeight * exp(-s_t)`  → use `integrable_dot_mul_dot_mul_rescaled_weight`
- `|B| * gaussianWeight`              → Gaussian moments
- `|B| * |c_t| * gaussianWeight`      → Gaussian moments + cubic growth of `cV`

Then gain `1/t` from the tail indicator:
```text
1_{‖u‖ ≥ ρ√t} ≤ ‖u‖² / (ρ² t).
```

That’s the cleanest tail trick here.

---

## Q2. Helpers 2/3
They are **easier** than helper 1.

Decompose
```text
φ((√t)⁻¹u) - (√t)⁻¹ dot d u = q_t(u) + r_t(u)
```
with `q_t := qφ((√t)⁻¹u)`, `|r_t| ≤ C‖u‖³/(t√t)` locally.

Then
- `∫ dot c · q_t · gW = 0` by parity
- the `q_t · (exp(-s_t)-1)` term only needs the **weak** `exp(-s)-1` estimate, since `q_t` already contributes `1/t`
- the `dot c · r_t · gW · exp(-s_t)` term is directly `O(1/(t√t))`

So yes: same skeleton, but less painful.

---

## Q3. Helper 4
Correct: **no parity needed**.

It is essentially weak helper 4 with the sharper local replacement
```text
|remφ| ≤ C‖u‖²/t + C'‖u‖³/(t√t)
|remψ| ≤ ...
```
hence on the local ball `≤ C''‖u‖²/t`, so product is `O(‖u‖⁴/t²)`.
Tail again by indicator trick.

---

## Q4. `h_decomp`
I would absolutely extract it:
```lean
private lemma rescaledNumerator_centered_pair_decomposition ...
```
Even if used once, it isolates 250–300 LOC of integral linearity/integrability noise and keeps the theorem readable.

---

## Q5. Scope
Your 1800 LOC estimate is realistic, but I’d expect more like:
- helper 1: 600–800 LOC
- helpers 2/3 together: 400–500 LOC
- helper 4: 250–350 LOC
- decomposition lemma: 200–300 LOC

So: **1500–1900 LOC** is a believable final bill. The main sink is helper 1.