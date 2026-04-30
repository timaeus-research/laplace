Short answer: **option 1 is the clean fix, and it’s not just a proof convenience — it’s mathematically necessary for your current API.**

### Why current hypotheses are too weak

Your obstacle is real. Under only `ObservableTensorApprox`, the lemma A bulk block can genuinely be only `O(t^{-1/2})`.

A concrete 1D counterexample:

- `ι = Fin 1`
- `H = 1`, `Hinv = 1`
- `V(w) = w^2 / 2`  
  so `rescaledPerturbation = 0`, hence `exp(-s_t) = 1`
- `ψ(w) = w`, so `b = 1`
- `φ(w) = w * |w|^3`

Then:

- `a = 0`
- `A = 0`
- `Φ = 0`
- `φ` still satisfies your current `ObservableTensorApprox` shape, since
  `|φ(w)| ≤ ‖w‖^4`

But now
\[
\phi((\sqrt t)^{-1}u)=\frac{u|u|^3}{t^2},
\qquad
\mu_\phi=0,
\]
so
\[
t\sqrt t \cdot (b\cdot u)\cdot \phi_{\rm conn,t}(u)
= t\sqrt t \cdot u \cdot \frac{u|u|^3}{t^2}
= \frac{|u|^5}{\sqrt t}.
\]
Hence
\[
t\sqrt t \int (b\cdot u)\phi_{\rm conn,t}(u)\,gW(u)\,du
= \frac{1}{\sqrt t}\int |u|^5 gW(u)\,du,
\]
which is **Θ(t^{-1/2})**, not `O(t^{-1})`.

So the bulk issue is not just a missing trick: **lemma A is false under the current `ObservableTensorApprox` assumptions**.

---

## What this means structurally

The bad term is exactly the **odd quartic part** of the observable remainder.

Your symmetrization analysis is right:

- even quartic remainder is harmless after multiplying by `(b·u)` because it becomes an odd kernel and cancels at Gaussian order,
- but an **odd quartic** remainder produces an even integrand already at size `t^{-1/2}`.

Current `Φ_jet_bound` only says `O(‖w‖^4)`, so it allows odd quartic remainder.

To get `O(t^{-1})`, you need to rule that out.

---

# Best fix: add `ObservableQuinticApprox`

The minimal analogue of `PotentialQuinticApprox` is exactly what you want.

I’d define:

```lean
structure ObservableQuinticApprox
    (φ : (ι → ℝ) → ℝ) (a : ι → ℝ)
    extends ObservableTensorApprox φ a where
  Q_const : ℝ
  Q_const_nn : 0 ≤ Q_const
  φ_odd_quintic_bound :
    ∀ w : ι → ℝ, ‖w‖ ≤ jet_radius →
      |φ w - φ (-w) - 2 * dot a w - (1 / 3 : ℝ) * Φ (fun _ => w)|
        ≤ Q_const * ‖w‖ ^ 5
```

For lemma A, since `a = 0`, this reduces to
\[
|\phi(w)-\phi(-w)-\tfrac13\Phi(w,w,w)| \le Q_\phi \|w\|^5.
\]

Then you get the key rescaled lemma:

```lean
|expNumObsRem φ 0 hφ t u - expNumObsRem φ 0 hφ t (-u)|
  ≤ Q_const * ‖u‖^5 / (t^2 * Real.sqrt t)
```

and your bad symmetrized term becomes

\[
t\sqrt t \cdot |b\cdot u| \cdot |r(u)-r(-u)|
\;\lesssim\;
\frac{\|u\|^6}{t},
\]

which is exactly the rate you need.

---

# Why this is cleaner than option 2

Option 2 would be:

- add a **quartic tensor** for `φ`,
- subtract the quartic term explicitly from `bulkErrA`,
- create a new odd degree-5 kernel with a `1/√t` prefactor,
- transport that kernel exactly like the odd block in lemma B.

That works in principle, but it is **strictly heavier**:

- more structure,
- more coefficient bookkeeping,
- more transport lemmas,
- but no benefit for the final coefficient, since quartic data does **not** appear in the theorem statement.

So if the theorem only needs the `t^{-2}` coefficient, **odd-quintic control is the right abstraction**.

---

# Why option 3 (IBP) is not the clean path

An IBP workaround would need derivative control on the remainder:
\[
\nabla r_t(u) = O(\|u\|^3/t^2),
\]
which indeed could recover `O(1/t)` after one Gaussian Stein step.

But your current API stores only **value** jets, not derivative bounds. So IBP would force a much more invasive redesign than adding an odd-quintic observable structure.

Also, the counterexample above shows you must exclude odd quartic remainder somehow anyway.

---

# Recommended change set

## 1. Add `ObservableQuinticApprox`

Only needed for the **second-order vanishing observable** `φ` in lemma A.

## 2. Strengthen lemma A and its callers

Change:

- `rescaledIntegral_cross_linear_connected_asymptotic`
- `rescaledNumerator_centered_pair_explicit`
- `gibbsCov_first_order_rate_explicit`

so that `hφ` is `ObservableQuinticApprox φ 0` (or more generally `ObservableQuinticApprox φ a` plus `a = 0`).

You do **not** need to strengthen `hψ`.

## 3. Add the observable analogue of the V-quintic rescaling lemma

Something like:

```lean
private lemma abs_expNumObsRem_sub_neg_quintic_le
    (hφ : ObservableQuinticApprox φ a) ...
```

and then finish the bulk block by the same symmetrization template you already wrote.

---

# Bottom line

- **Current structure is insufficient.**
- **Lemma A is actually false under `ObservableTensorApprox` alone.**
- The cleanest minimal repair is **option 1**:
  add `ObservableQuinticApprox` with an odd-quintic bound.

If you want, I can draft the exact Lean structure + the two key lemmas:
1. the rescaled odd-quintic remainder bound for `expNumObsRem`,
2. the final `abs_integral_bulkErrA_le` proof skeleton using your existing `bulkErrA_symmetric`.