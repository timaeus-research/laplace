Short version: the cheapest proof is **not** “upgrade the old sharp cross bound”. That bound is sitting exactly at the size of the new main term. The cheap route is:

1. **peel off the scalar quadratic mean of** `φ`,
2. reuse the **Stage-4 expectation theorem** for the resulting scalar piece,
3. prove exactly **two new asymptotic lemmas** for the genuinely connected pair pieces.

That is the minimal clean decomposition.

---

## Recommended decomposition

Write, for `u` in the scaled variable,

- `φ_t(u) := φ((√t)⁻¹ • u)`
- `ψ_t(u) := ψ((√t)⁻¹ • u)`
- `Lψ(u) := dot b u`
- `Qφ(u) := (1/2) uᵀ A_φ u`
- `Qψ(u) := (1/2) uᵀ A_ψ u`
- `Cφ(u) := (1/6) Φ_φ(u,u,u)`

Since `a = 0`, the Stage-4 coefficient for `φ` is just

- `μ_φ = (1/2) tr(A_φ Σ)`.

Now define the **Gaussian-centered quadratic**
- `Qφᶜ(u) := Qφ(u) - μ_φ`.

Then expand `φ_t` as
- `φ_t = μ_φ/t + φ_t_conn`,
where
- `φ_t_conn = t⁻¹ Qφᶜ + t^(-3/2) Cφ + Eφ_t`,
with `Eφ_t = O(‖u‖⁴/t²)` and, importantly, its **odd part** is `O(‖u‖⁵/t^(5/2))`.

Also write
- `ψ_t = t^(-1/2) Lψ + ψ_t_rem`,
with
- `ψ_t_rem = t⁻¹ Qψ + Eψ_t`,
where `Eψ_t = O(t^(-3/2)‖u‖³ + t⁻²‖u‖⁴)`.

Then the numerator piece decomposes as

\[
t^2 N_t(\phi\psi)
=
\mu_\phi \cdot \bigl(t\,N_t(\psi)\bigr)
\;+\;
t^{3/2} \!\int L_\psi\, \phi_{t,\mathrm{conn}}\, g_W e^{-s_t}
\;+\;
t^2 \!\int \phi_{t,\mathrm{conn}}\, \psi_{t,\mathrm{rem}}\, g_W e^{-s_t}.
\]

So

\[
t^2 N_t(\phi\psi) - (\mu_\phi\mu_\psi + c_{\mathrm{cross}} + c_{QQ})D_t
\]

splits into exactly:

1. **old Stage-4 piece**
   \[
   \mu_\phi\cdot\bigl(t N_t(\psi)-\mu_\psi D_t\bigr)
   \]
2. **new cross asymptotic**
   \[
   t^{3/2}\!\int L_\psi\,\phi_{t,\mathrm{conn}}\,g_W e^{-s_t}
   \;-\;
   c_{\mathrm{cross}} D_t
   \]
3. **new quadratic-quadratic asymptotic**
   \[
   t^2\!\int \phi_{t,\mathrm{conn}}\,\psi_{t,\mathrm{rem}}\,g_W e^{-s_t}
   \;-\;
   c_{QQ} D_t.
   \]

Here
- `c_QQ = (1/2) tr(A_φ Σ A_ψ Σ)`
- `c_cross = (1/2) <Σb, Φ_φ:Σ> - (1/2)<b, A_φ Σ T:Σ> - (1/2)<Σb, T:(ΣA_φΣ)>`

and then
- `μ_φ μ_ψ + c_cross + c_QQ = cov2_full`.

This is the cleanest coefficient bookkeeping, because centering `Qφ` removes the disconnected trace piece from the cross Wick contraction.

---

## Why this is cheaper than using `pair_product_expansion` verbatim

Your existing sharp decomposition gives, schematically,

\[
t^2(\phi_t\psi_t)
=
t I_1 + t^{3/2} I_2 + t^{3/2} I_3 + t^2 I_4.
\]

With `a=0`:
- `I_1 = 0`
- `I_2 = 0`
- only `t^(3/2) I_3` and `t^2 I_4` survive.

So **yes**, it is still a useful scaffold. But it is *not* the cheapest final organization, because it leaves you with uncentered coefficients and uglier algebra. The scalar split
`φ_t = μ_φ/t + φ_t_conn`
is cheaper in Lean than carrying the disconnected trace terms through the `I_3` Wick contraction.

So my recommendation is:

- use the sharp-style pair split only **after** peeling `μ_φ/t`,
- not directly on raw `φ_t`.

---

## Where the connected terms live

### In the cross piece
\[
t^{3/2}\int L_\psi\,\phi_{t,\mathrm{conn}}\,g_W e^{-s_t}
\]

expand
- `φ_t_conn = t⁻¹ Qφᶜ + t^(-3/2) Cφ + Eφ_t`.

Then the only order-1 contributions after scaling are:

1. `Lψ · Cφ · 1`
   gives  
   \[
   \frac12 \langle \Sigma b,\; \Phi_\phi:\Sigma\rangle
   \]

2. `Lψ · Qφᶜ · ( - V_3 / √t )`
   gives  
   \[
   -\frac12 \langle b,\; A_\phi \Sigma\, T:\Sigma\rangle
   -\frac12 \langle \Sigma b,\; T:(\Sigma A_\phi \Sigma)\rangle.
   \]

That is exactly the non-QQ connected part.

### In the remainder×remainder piece
\[
t^2\int \phi_{t,\mathrm{conn}}\,\psi_{t,\mathrm{rem}}\,g_W e^{-s_t}
\]

the only order-1 contribution is
- `Qφᶜ · Qψ · 1`

which gives
\[
\frac12 \operatorname{tr}(A_\phi \Sigma A_\psi \Sigma).
\]

So the four connected terms split as:

- 3 terms in the cross lemma,
- 1 term in the rr lemma.

That is the best modular split.

---

## Answers to your four sub-questions

### 1. Can `pair_product_expansion` still be used directly?
**Yes, as an outer scaffold.**  
But I would not use it *verbatim* as the final organization.

With `a=0`, it reduces to the two surviving pieces:
- `t^(3/2)` times the `dot b · remφ` term,
- `t²` times the `remφ · remψ` term.

That is already good structurally. But the **cheapest** proof is to first split off `μ_φ/t`, then use the sharp-style pair split only on the connected remainder of `φ`.

So: **useful, yes; optimal, no.**

---

### 2. Where do the connected `cov2` terms appear?
- In `dot b · remφ`:
  - `cubic observable × linear ψ` gives `+(1/2)<Σb, Φ_φ:Σ>`
  - `quadratic observable × linear ψ × cubic potential` gives the two `T` contractions
- In `remφ · remψ`:
  - `quadratic × quadratic` gives `(1/2) tr(A_φ Σ A_ψ Σ)`.

To extract them at `t⁻²` accuracy, you need a **real asymptotic expansion lemma**, not just the old absolute bound. The old `K/(t√t)` bound is exactly the size of the main cross term before you multiply by `t^(3/2)`.

---

### 3. Can the sharp cross helper be upgraded from `K/(t√t)` to `K/t²` just because `a=0`?
**No.** Not in the generic form.

The reason is conceptual: that integral is **not smaller** when `a=0`; it now contains the new order-`t^(-3/2)` main term:
- from `Lψ · Cφ`
- and from `Lψ · Qφ · (-V_3/√t)`.

So the old helper is not “imprecise”; it is stopping exactly at the right magnitude for Stage 1. For Stage 5, you must extract the explicit constant.

What you *can* upgrade is this:

> replace the old pure bound by a **specialized asymptotic lemma**
> \[
> \left| t^{3/2}\int L_\psi\,\phi_{t,\mathrm{conn}}\,g_W e^{-s_t}
> - c_{\mathrm{cross}} D_t \right|\le K/t.
> \]

That is the right new statement.

---

### 4. Do you need entirely new sub-lemmas?
**Yes, but only two essential asymptotic ones** if you organize it well.

#### New lemma A: cross asymptotic
A specialized lemma for
\[
t^{3/2}\int L_\psi\,\phi_{t,\mathrm{conn}}\,g_W e^{-s_t}.
\]

Main terms:
- `Lψ Cφ`
- `-Lψ Qφᶜ V3`

Everything else is error.

#### New lemma B: rr asymptotic
A specialized lemma for
\[
t^2\int \phi_{t,\mathrm{conn}}\,\psi_{t,\mathrm{rem}}\,g_W e^{-s_t}.
\]

Main term:
- `Qφᶜ Qψ`

Everything else is error.

---

## The genuinely new supporting infrastructure

If not already present, the only really valuable small helpers are:

1. **Centered quadratic moment formulas**
   - `∫ Qφᶜ Qψ gW = (1/2) tr(A_φ Σ A_ψ Σ)`
   - `∫ Lψ Cφ gW = (1/2)<Σb, Φ_φ:Σ>`
   - `∫ Lψ Qφᶜ V3 gW = (1/2)<b, A_φΣ T:Σ> + (1/2)<Σb, T:(ΣA_φΣ)>`

2. **Parity-aware remainder facts**
   - odd part of `Eφ_t` is `O(‖u‖⁵/t^(5/2))`
   - enough to kill the dangerous `Lψ * Eφ_t` term at the right rate.

3. **Weight expansion with parity**
   You want something like:
   \[
   e^{-s_t} = 1 - t^{-1/2}V_3 + t^{-1}U_{\mathrm{even}} + O(t^{-3/2}\,\text{poly}),
   \]
   where the `t^{-1}` correction is explicitly **even**.
   Then:
   - in the cross lemma, the `U_even` term drops against the odd integrand,
   - in the rr lemma, the `-V_3/√t` term drops against the even integrand.

That parity packaging is what keeps the proof short.

---

## Cheapest possible statement shape for the two new lemmas

If I were minimizing Lean friction, I would state:

### Lemma 1: connected linear-cross asymptotic
For `a = 0`, with `φ_conn_t = φ_t - μ_φ/t`,
\[
\left|
t^{3/2}\int L_\psi \,\phi_{t,\mathrm{conn}}\, g_W e^{-s_t}
-
c_{\mathrm{cross}} D_t
\right|
\le \frac{K}{t}.
\]

### Lemma 2: connected rr asymptotic
With `ψ_rem_t = ψ_t - t^{-1/2}L_\psi`,
\[
\left|
t^2\int \phi_{t,\mathrm{conn}}\,\psi_{t,\mathrm{rem}}\, g_W e^{-s_t}
-
\frac12\operatorname{tr}(A_\phi\Sigma A_\psi\Sigma)\,D_t
\right|
\le \frac{K}{t}.
\]

Then final helper is literally:
- Stage-4 singleton asymptotic for `ψ`,
- plus Lemma 1,
- plus Lemma 2,
- plus coefficient identity.

That is the cheapest modular route.

---

## LOC reality check

### If these already exist:
- Stage-4 explicit expectation theorem with `|t·N_t(ψ)-μ_ψ D_t| ≤ K/t`
- denominator estimate `|D_t - 1| ≤ K/t`
- Gaussian moment lemmas for `QᶜQ`, `LC`, `LQᶜV3`
- one parity-friendly weight expansion lemma

then **yes**, I think this can land in roughly **200–300 LOC**.

### If any of these are missing:
especially
- the `LQᶜV3` Wick contraction lemma, or
- the parity/odd-part remainder lemma for `Eφ_t`,

then expect **400–700 LOC**, with the cross lemma being the cost center.

So: **under 300 LOC is plausible only with the centered-quadratic split and existing polynomial/Gaussian infrastructure**. Without that, I would budget **well over 300**.

---

## Final recommendation

If your Stage-4 expectation theorem is already at the same `O(1/t)` rate after scaling by `t`, do this:

1. **Split `φ_t = μ_φ/t + φ_t_conn` first.**
2. Reuse Stage-4 for `μ_φ * t N_t(ψ)`.
3. Prove only:
   - `cross_linear_connected_asymptotic`
   - `rr_connected_asymptotic`
4. Rewrite coefficients to `cov2_connected + μ_φ μ_ψ`.

That is the cheapest proof plan.

If you want, I can also sketch the proof skeleton for those two new lemmas in the exact order I’d formalize them in Lean.