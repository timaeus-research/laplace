Here’s the short version:

## 1. Q1: your `M(t)` analysis is too crude; `O(1/√t)` is still the right weak rate

The issue is not the theorem statement; it’s the bound you used.

The right split is **not** at a fixed ball or a slowly growing `M(t)`.  
It is at the **natural Taylor-validity radius**:

\[
\|u\| \le \delta \sqrt t
\]

for some fixed small `δ > 0`.

Also, the local bound should not be used as

\[
|e^{-s_t}-1| \le |s_t| e^{|s_t|}
\]

followed by throwing away the Gaussian. You need to **absorb** the `e^{|s_t|}` into Gaussian decay.

### Key missing lemma
From `PotentialApprox` alone, you can prove a **global quadratic lower bound** for the Gaussian quadratic form:

\[
\exists \kappa_H>0,\quad \forall u,\quad \frac12\,\mathrm{quadForm}\,H\,u \ge \kappa_H \|u\|^2.
\]

Why? For small `w`,

\[
\frac12 q_H(w) \ge V(w) - C\|w\|^3 \ge (c - Cr)\|w\|^2
\]

if `‖w‖ ≤ r` and `r` is chosen so that `Cr ≤ c/2`. Then use homogeneity of the quadratic form to scale from radius `r` to all `u`.

Once you have that, set

- `A_t(u) := t * V ((√t)⁻¹ • u)`
- `B(u) := (1/2) * quadForm H u`

Then on `‖u‖ ≤ δ√t` with `δ` small enough,

\[
|s_t(u)| = |A_t(u)-B(u)| \le C \frac{\|u\|^3}{\sqrt t}
\le C\delta \|u\|^2.
\]

Choose `δ` so that `Cδ ≤ κ_H/2`. Then

\[
gW(u)\, e^{|s_t(u)|}
\le e^{-\kappa_H\|u\|^2} e^{(\kappa_H/2)\|u\|^2}
= e^{-(\kappa_H/2)\|u\|^2}.
\]

So locally,

\[
|gW(u)(e^{-s_t(u)}-1)|
\lesssim \frac{\|u\|^3}{\sqrt t}\, e^{-(\kappa_H/2)\|u\|^2}.
\]

That integrates to `O(1/√t)`.

### Tail
Outside `‖u‖ ≤ δ√t`, both the Gaussian reference and the rescaled Gibbs weight have quadratic decay, so the tail is actually **exponentially small in `t`**:

\[
\int_{\|u\|>\delta\sqrt t} e^{-\alpha \|u\|^2}\,du
\le C e^{-\alpha' t}.
\]

So the partition error is

\[
O(t^{-1/2}) + O(e^{-\alpha t}) = O(t^{-1/2}).
\]

So: **yes, `K/√t` is the correct weak partition rate under your hypotheses.**  
The log-loss comes from a suboptimal split/bound.

---

## 2. Q2: yes, you need higher moments — but do **not** add them to `LaplaceCovHypotheses`

You need more than second moments.

Roughly:

- partition: cubic moment,
- single observable: up to 4th moment,
- pair observable: up to 5th moment,
- tails: arbitrary polynomial degree, because `HasPolyGrowth` uses an arbitrary exponent `p`.

So adding “3rd moments” to `LaplaceCovHypotheses` is not the right abstraction.

## Recommended fix
Add a **generic coercive-Gaussian polynomial domination package**, e.g.

- `Integrable (fun u => ‖u‖^n * exp (-α * ∑ i, u i^2))` for all `n : ℕ`,
- and a tail version
  \[
  \int_{\|u\|>\delta\sqrt t} (1+\|u\|^n)e^{-\alpha\|u\|^2}\,du
  \le C_n e^{-\beta t}.
  \]

That is the right reusable layer.

### Lean-wise
You can avoid nasty coordinate-by-coordinate odd/even sign lemmas by proving scalar bounds of the form

\[
x^m e^{-\alpha x} \le C e^{-(\alpha/2)x}, \qquad x\ge 0,
\]

and then apply with `x = ∑ i, u_i^2`, using `‖u‖² ≤ ∑ i, u_i²`.

That’s much cleaner than adding ad hoc 3rd/4th/5th coordinate moments.

---

## 3. Q3: order of attack

Yes: **do numerator first**, then quotient.

I’d structure it like this:

### Step A: add auxiliary lemmas
1. `quadForm_lower_bound` from `PotentialApprox`
2. `gaussianWeight_le_exp_neg_const_sq`
3. generic polynomial-Gaussian integrability/tail lemmas
4. `abs_dot_le_const_mul_norm`:
   \[
   |\langle a,u\rangle| \le \Big(\sum_i |a_i|\Big)\|u\|.
   \]

### Step B: denominator
Prove partition asymptote:

\[
|D_t - Z| \le K/\sqrt t.
\]

Then derive a lower bound:

\[
D_t \ge Z/2
\]

for all large `t`.

### Step C: numerator lemmas
Prove separately:

- `|N_t(φ)| ≤ K/t`
- `|t N_t(φψ) - Z * dot a (Hinv b)| ≤ K/√t`

This is cleaner than proving expectation statements directly.

### Step D: quotient lemmas
Then use

\[
E_t = N_t / D_t.
\]

For the pair,

\[
tE_t - m
= \frac{tN_t - Zm}{D_t} + m \frac{Z-D_t}{D_t},
\quad m = \langle a, Hinv\, b\rangle.
\]

With `D_t ≥ Z/2`, this is immediate.

So yes: **split observable/pair into numerator theorem + denominator lower bound + quotient lemma.**

---

## 4. Q4: don’t weaken the theorem statement yet

I would **not** change the three statements.

Mathematically, your current weak-rate statements are honest:

- partition: `O(t^{-1/2})`
- single observable: `O(t^{-1})`
- pair: `t * E_t - main = O(t^{-1/2})`

What’s missing is not weaker asymptotics; it’s the **moment/tail infrastructure** and the **quadratic lower bound for `quadForm H`**.

If you refuse to add those lemmas, then you can probably still prove qualitative convergence, but that would be a bad stopping point relative to the rest of the file.

---

## 5. Skeleton of one achievable proof: partition

Let

\[
D_t := \text{rescaledPartition } V t,\qquad
Z := gaussianZ\, H.
\]

Using your lemma:

\[
D_t - Z
= \int gW(u)\,(e^{-s_t(u)}-1)\,du.
\]

Choose `κ_H > 0` with

\[
\frac12\,quadForm\,H\,u \ge \kappa_H \|u\|^2.
\]

Choose `δ > 0` with

- `δ ≤ hV.local_radius`
- `hV.local_const * δ ≤ κ_H / 2`.

Split into

- local: `‖u‖ ≤ δ√t`
- tail: `‖u‖ > δ√t`.

### Local part
On the local region,

\[
|s_t(u)| \le C \frac{\|u\|^3}{\sqrt t} \le C\delta \|u\|^2.
\]

Then with `abs_exp_neg_sub_one_le`,

\[
|gW(e^{-s_t}-1)|
\le gW \, |s_t| e^{|s_t|}
\le \frac{C}{\sqrt t}\|u\|^3 e^{-(\kappa_H/2)\|u\|^2}.
\]

Integrate: `≤ K_loc / √t`.

### Tail part
Use your uniform bound plus quadratic decay:

\[
|gW(e^{-s_t}-1)|
\le gW + e^{-c\|u\|^2}
\le e^{-\kappa_H\|u\|^2} + e^{-c\|u\|^2}.
\]

On `‖u‖ > δ√t`,

\[
e^{-\alpha\|u\|^2}
\le e^{-\alpha \delta^2 t/2} e^{-(\alpha/2)\|u\|^2}.
\]

So tail is `≤ K_tail e^{-β t}`.

Combine, and for `t ≥ 1`, absorb the exponential term into `K/√t`.

---

## Bottom line

- **Q1:** `O(1/√t)` is still right; the log-loss is an artifact of a crude split.
- **Q2:** yes, you need higher moments, but derive them generically from coercivity/poly-growth; don’t add them to `LaplaceCovHypotheses`.
- **Q3:** prove denominator, then numerator lemmas, then quotient.
- **Q4:** keep the current statements.
- **Q5:** the partition proof above is the clean template; the observable/pair proofs follow the same local-vs-tail pattern.

If you want, I can next help you write the exact lemma list I’d add to `RescaledIntegrals.lean` so the three sorries become mostly bookkeeping.