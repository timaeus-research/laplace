**A → B → C is the right dependency chain.** The existing uniform Gaussian domination makes this a good place to switch from bespoke asymptotic estimates to one general dominated-convergence theorem.

## 1. A: dominated convergence versus rate machinery

**Use dominated convergence for `tendsto_J_n`.** For each fixed `n`, the bound you already have gives, eventually in `t`,
\[
\left|u^n e^{-u^2/2}e^{-r(t,u)}\right|
\le |u|^n e^{-c_0u^2}.
\]
The right-hand side is integrable for every natural `n`. This is exactly the reusable argument needed to cover all moments.

The pointwise limit has no mathematical subtlety:
\[
\frac1{\sqrt t}\to0,\qquad \frac1t\to0
\quad\Longrightarrow\quad
r(t,u)\to0
\quad\Longrightarrow\quad
e^{-r(t,u)}\to1.
\]
In Lean, I would isolate this in a small helper lemma, then obtain the integrand limit by multiplication by the fixed factor `u^n * exp (-u^2 / 2)`.

The formalization details to watch are:

- Work **eventually with `t > 0`**, rather than imposing domination for all real `t`.
- Supply the measurability hypotheses separately; the integrands are continuous in `u` for fixed positive `t`.
- Use an integrability lemma for **`|u|^n` times a Gaussian**, since odd powers cannot themselves serve as a nonnegative dominator.
- Dominate the **whole Boltzmann factor**, not `exp (-r)` alone: the cubic perturbation can make the latter large.

The rate machinery may generalize, but **not as a `K/t` bound for every `n`**. Generically,
\[
J_{2k}(t)-G_{2k}=O(t^{-1}),\qquad
J_{2k+1}(t)=O(t^{-1/2}),
\]
where \(G_n=\int u^n e^{-u^2/2}\,du\). The even rate uses cancellation of the first-order cubic term; the odd first-order term generally survives. Thus a rate-based generalization introduces parity and remainder estimates that A does not need. Unless those estimates are already packaged abstractly, A is the cheaper and cleaner foundation.

## 2. B: quotient identity and statement shape

For `t > 0`, write \(s=\sqrt{\lambda t}>0\). Your change-of-variables identities say
\[
J_n=s^{n+1}I_n,\qquad J_0=sI_0.
\]
Consequently,
\[
s^n\frac{I_n}{I_0}=\frac{J_n}{J_0}.
\]
Then apply the quotient-limit theorem using
\[
J_n\to G_n,\qquad J_0\to\sqrt{2\pi}\ne0.
\]

Beyond what you list, the relevant algebraic side condition is **`s ≠ 0`**, obtained from `λ > 0` and `t > 0`. Positivity of `I₀` is the natural fact to use if proving the identity by `field_simp`; it also validates the probabilistic normalization. Strictly speaking, with Lean’s totalized division, the identity can be proved by cancelling the nonzero scale without assuming `I₀ ≠ 0`. Either route is fine—reuse existing partition-function positivity if available.

**State the core theorem using `Real.sqrt (lam * t) ^ n`.** This aligns directly with the seabed relation and avoids real-power side conditions and rewriting overhead. A real-power version can be a later presentation corollary.

For downstream use, provide the even specialization
\[
t^k\langle x^{2k}\rangle_t
\longrightarrow \frac{(2k-1)!!}{\lambda^k}.
\]
Its conversion from the square-root form uses only natural-power algebra and `sqrt_sq` on the eventual positive tail.

## 3. Which odd-moment theorem?

**For this tide, retain the Gaussian-scale zero limit**
\[
\sqrt{\lambda t}^{\,2k+1}\langle x^{2k+1}\rangle_t\to0.
\]
It follows immediately from B and the odd Gaussian integral, so it is a nearly free part of the all-orders API.

The sharper statement is valuable, but is a separate first-order theorem:
\[
t^{k+1}\langle x^{2k+1}\rangle_t
\longrightarrow
-\frac{\alpha(2k+3)!!}{6\lambda^{k+2}}.
\]
Indeed, the first surviving numerator term is
\[
J_{2k+1}(t)
=-\frac{A}{\sqrt t}\,G_{2k+4}+o(t^{-1/2}).
\]
Justifying this requires a dominated difference quotient or a controlled expansion, not merely the domination used in A. It would unify the existing first- and third-moment results, but **is unnecessary for the stated covK gap**.

In particular, letting \(S_n(t)=\sqrt{\lambda t}^{\,n}\langle x^n\rangle_t\),
\[
t^2\langle x^5\rangle_t
=\lambda^{-5/2}t^{-1/2}S_5(t)\to0.
\]
Even eventual boundedness of \(S_5\) suffices. Likewise,
\[
t^3\langle x^6\rangle_t\to15/\lambda^3
\quad\Longrightarrow\quad
t^2\langle x^6\rangle_t\to0.
\]
General eventual boundedness should be extracted from B’s convergence, not proved by another integral estimate.

## Vote

**Formalize A, B, and C**, in that order:

- **A:** one all-orders dominated-convergence theorem.
- **B:** square-root/natural-power normalization, with even and odd corollaries.
- **C:** the three fifth/sixth-moment consequences and general eventual boundedness, as thin corollaries.

**Defer general rates and sharp odd-moment constants.** They are a worthwhile later extension, not prerequisites for closing the covK moment gap.