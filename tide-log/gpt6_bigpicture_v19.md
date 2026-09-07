## Recommendation: open (B), with a short, explicit feasibility gate

The deterministic normal-block programme is complete enough to stand on its own. **The highest-value next step is now the stochastic \(1/\log N\) posterior theorem**, rather than another extension of its deterministic backend.

It connects the machinery already formalised to a genuinely new probabilistic conclusion for the paper. More importantly, your inventory suggests that the remaining difficulty is concentrated: **joint coefficient convergence and the correctly scaled numerator remainder**, not a new asymptotic calculus.

I would authorise **two scoping units, then implementation if the gate below passes**. Keep (A) as the bounded fallback—not as a prerequisite.

### Ranking and planning estimates

These are estimates of proof units, conditional on the interfaces described in your message, rather than an inspection of the current repository.

| Rank | Programme | Estimate | Assessment |
|---|---|---:|---|
| **1** | **B: stochastic \(1/\log N\) regime** | **1–2 scoping + 8–15 implementation** | Best paper-facing payoff; substantial existing backend. Could contract if the joint array theorem already supplies exactly the required pair. |
| **2** | **A: signed-reflection amplitudes** | **3–5** | Very safe, self-contained completion of the symmetric-box story. Excellent fallback or subsequent short programme. |
| **3** | **D: general-\(d\) leading random-phase term, without Taylor arrays** | **2 scoping + 5–9 implementation** | Plausible cheaper route exists, but requires a new rescaled-measure or kernel-testing interface. |
| **4** | **C, narrowly: unequal-exponent quadratic charts at zero phase** | **1–3 for a dictionary corollary; 3–6 if chart bookkeeping is substantial** | Now tractable using mixed ratios. Valuable if it closes an explicit paper statement; otherwise mostly repackaging. |
| **5** | **E: first subleading logarithmic coefficient** | **2 scoping + 8–15**, restricted model | A real new analytic programme, not a routine continuation of the leading term. |
| **6** | **C, in full: TaylorTree / Mellin / general tree expansion / SLT application** | **Several programmes; likely dozens of units** | Still not an appropriate next autonomous target. General-\(d\) leading monomial asymptotics do not remove its principal dependencies. |

If the unequal-exponent corollary directly discharges a currently missing author-facing equation, it can move ahead of D as a short closure task.

---

## B: first-unit statement and feasibility gate

### First unit: the log-scale posterior transfer interface

Use a deterministic positive common scale \(a_N\), and write
\[
D_N=\frac{Z_{1,N}}{a_N},
\qquad
U_N=\frac{\log N\,Z_{\varphi,N}}{a_N}.
\]

The first theorem should have this shape:

> Suppose coefficient pairs satisfy
> \[
> (B_N,A_N)\Rightarrow(B,A),
> \]
> and the residual vector satisfies
> \[
> (U_N-B_N,\;D_N-A_N)\xrightarrow{\mathbb P}(0,0).
> \]
> If \(A>0\) almost surely, then
> \[
> \log N\,\frac{Z_{\varphi,N}}{Z_{1,N}}
> \Rightarrow \frac BA.
> \]

The desired instantiation is
\[
(B,A)=\bigl(B_p^\varphi(X),A_p^1(X)\bigr).
\]

This should **reuse** the existing positive-denominator quotient theorem and joint Slutsky machinery. It is an interface theorem, not a reason to rebuild either. If it is already an immediate existing specialisation, count the first unit as the chart-specific instantiation and hypothesis ledger instead.

The crucial residual hypotheses, expressed before introducing \(U_N,D_N\), are
\[
Z_{\varphi,N}-\frac{a_N}{\log N}B_N
   =o_{\mathbb P}\!\left(\frac{a_N}{\log N}\right),
\]
\[
Z_{1,N}-a_NA_N=o_{\mathbb P}(a_N).
\]

**The numerator estimate is the gate.** A remainder known only to be \(o_{\mathbb P}(a_N)\) is insufficient.

### What the two scoping units must establish

1. **Cancellation is valid for the stochastic phase family.**  
   Identify the exact theorem giving \(A_p^\varphi(X)=0\), not merely its zero-phase version. Also distinguish vanishing at the corner from vanishing on the coefficient-supporting face. Those coincide in some equal-ratio settings, but not generally.

2. **The existing remainder theorem has the needed normalization.**  
   Trace the actual powers and logarithms through `normA'`, `normB'`, and `chart_posterior_tendsto_log`. The deterministic posterior theorem alone does not supply stochastic remainder control.

3. **Joint convergence comes from the same random input.**  
   Obtain the vector \((B_N,A_N)\) from a common coefficient-array or phase limit. Separate marginal convergence is not enough; independence is neither expected nor needed.

4. **The coefficient and positivity interfaces match.**  
   Check continuity/measurability for the joint map and almost-sure strict positivity of the limiting denominator. A deterministic lower bound is not required.

**Proceed if these obligations are existing results or short adaptations.** If the numerator remainder instead requires a new uniform random-field expansion, stop the implementation phase, record that dependency precisely, and open A. That preserves autonomous progress without silently turning B into D or the full Taylor-tree programme.

---

## A: an excellent short programme, with a carefully bounded headline

I would retain your **3–5 unit** estimate:

1. Orthant/reflection integral identity.
2. Continuity of the signed symmetrisation.
3. Evaluation
   \[
   \eta_{\rm sym}(0)
   =\eta(0)\prod_i(1+(-1)^{h_i}).
   \]
4. Symmetric-box leading asymptotic.
5. Optional author-facing parity corollary.

The headline should say:

> **An odd exponent annihilates the equal-ratio leading corner coefficient for the reflection-invariant monomial kernel.**

Do not inadvertently claim that the entire integral vanishes for an arbitrary amplitude. Nor does this automatically give cancellation for a nonsymmetric nonzero random phase.

This is useful mathematical closure, but B is the more consequential next theorem.

---

## D: yes, there is a plausible route avoiding multi-index arrays

For the **leading term only**, I would investigate a rescaled-measure formulation rather than a \(d\)-dimensional `ampCoeff` construction.

Set \(s=N\prod_i u_i^{k_i}\). The proposed extension should allow testing the rescaled monomial measure against functions of both \(s\) and \(u\), including
\[
F(s,u)=e^{-\beta s^2+\beta s\xi(u)}\eta(u).
\]

The limiting coefficient then evaluates \(\xi\) and \(\eta\) on the relevant supporting face and integrates against the limiting \(s\)-density.

The proof architecture is:

* convergence for compactly supported tests in the rescaled variable;
* concentration onto the appropriate face;
* Gaussian domination to remove the \(s\)-cutoff.

For bounded \(\xi\) and \(\beta>0\),
\[
-\beta s^2+\beta s\xi(u)
\le -\frac{\beta}{2}s^2+\frac{\beta}{2}\|\xi\|_\infty^2.
\]
Thus **smallness and analyticity are not inherently necessary for this deterministic leading-term argument**. Continuity on a compact box and boundedness may suffice.

Two cautions:

* This is **not** a direct application of the fixed continuous-amplitude theorem: the substituted amplitude depends on \(N\) through \(s\). A new testing/uniformity lemma is the essential work.
* With mixed ratios, the phase generally survives as a function on the supporting face, not just as \(\xi(0)\). For stochastic transfer, bounds uniform on suitable bounded or compact phase families are an additional obligation.

At zero phase, explicitly cross-check the \(N^2\) substitution, including
\[
\log(N^2)=2\log N.
\]

This route could establish a valuable **general-\(d\) leading-term theorem**, but should not be labelled a proof of full `thm:TaylorTree`.

---

## C and E: what is actually unlocked?

**Now tractable from C:** zero-phase unequal-exponent quadratic charts, and leading-term surrogates of standard-integral statements whose hypotheses reduce to the completed monomial model. Mixed ratios also determine whether a logarithm occurs: the multiplicity of the minimal ratio matters.

**Not automatically unlocked:** meromorphic continuation, full multivariate expansions, general fluctuating tree terms, the specific \(\Delta\)-boundary estimate, or the SLT application. Each still needs a separate dependency audit.

For E, distinguish two targets:

* the next logarithmic coefficient associated with the **same pole**;
* the contribution from the **next distinct pole**.

They are not interchangeable. Moreover, continuity alone generally gives no controlled \(1/\log N\) relative remainder. A subleading programme needs stronger amplitude assumptions and explicit subtraction/remainder estimates. Start with a tightly restricted model if and when E is opened.

---

## Report: hand it to the authors now

**Do not wait for the next programme.** Send the consolidated normal-block report as a completed, independently useful deliverable.

Accompany it with a short status note:

* pinned formalisation commit: `2674a29`;
* reported build status and zero `sorry`/axiom status;
* reviews v2–v5 clean;
* **unit 193 v6 review pending**;
* subsequent programmes explicitly outside this report’s scope.

Freeze this report version; issue a small revision if v6 requests changes. Pending review should be disclosed, but it is not a reason to couple delivery of a closed programme to the first success of an unrelated one.

**Operational instruction: deliver the report, open B’s two-unit gate, and fall back to A only if that gate exposes a genuinely missing stochastic expansion.**
