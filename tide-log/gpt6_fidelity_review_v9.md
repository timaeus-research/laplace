## Verdict

**The supplied theorem statements have the correct hypotheses, scales and constants.** No mathematical statement-level defect found in units 198–203, interpreting the omitted definitions by their documented formulas. The principal fidelity issue is the documentation’s reuse of \(S\) for a moment that is **half the paper’s \(S\)**.

### 1. Headlines and normalisations

- **Unit 198: unequal exponents — correct.** The assumptions imply \(0<p_1<p_2\), and
  \[
  h_2+1-p_1k_2=k_2(p_2-p_1)>0.
  \]
  Thus the stated limit is
  \[
  \frac{\Gamma(p_1/2)\beta^{-p_1/2}}
       {2k_1k_2(p_2-p_1)}
  =\frac{\Gamma(p_1/2)}
       {2k_1\beta^{p_1/2}(h_2+1-p_1k_2)}.
  \]
  The swapped headline is correct too. The dictionary uses the **same parameter \(n\)**, so there is no logarithmic transport factor.

- **`noLogConst_zeroPhase_eq` — correct.** Reversing integration gives
  \[
  \frac1{p_2-p_1}\int_0^\infty t^{p_1-1}e^{-\beta t^2}\,dt
  =\frac{\Gamma(p_1/2)\beta^{-p_1/2}}{2(p_2-p_1)}.
  \]
  Mathematically this holds for all \(0<p_1<p_2\); the Lean theorem is restricted to ratios realised by natural-number data, as the mirror explicitly acknowledges.

- **Unit 200: shifted terms — correct.** The shift adds \(j/2\) to every ratio and preserves the minimising face and residual weight. The factor \(N^j\) cancels the shifted power of \(N\); transporting the logarithm contributes \(2^{m-1}\). For the actual exponential Taylor term, additionally multiply by \(\beta^j/j!\) and use amplitude \(\xi^j\eta\).

- **Units 202–203: phase headline — correct.** Positive dimension, \(k_i>0\), \(\beta>0\), positive attained minimum \(\lambda\), and continuous phase/amplitude are sufficient. In particular, for \(i\notin J\),
  \[
  h_i-2k_i\lambda>-1,
  \]
  ensuring integrability of the residual weight. The coefficient is exactly
  \[
  \frac{\displaystyle\int\eta(\pi u)\,
       \operatorname{phaseMoment}_{\beta,2\lambda}(\xi(\pi u))
       \,\mathrm{residualWeight}(u)\,du}
       {(m-1)!\prod_{i\in J}k_i}.
  \]
  The factor audit is \(2^{m-1}\cdot2\cdot2^{-m}=1\).

- **Equal ratios — correct.** The face is the corner and the unit box has volume one, giving
  \[
  \frac{\eta(0)\operatorname{phaseMoment}_{\beta,p}(\xi(0))}
       {(d-1)!\prod_i k_i}.
  \]
  For \(d=2\), this is precisely \(A_p\) in the variable \(N\).

- **Moment dictionary — correct mathematically:**
  \[
  \operatorname{phaseMoment}_{\beta,p}(a)
  =J_p(a)=\tfrac12S_{p/2}(a),
  \]
  by \(t=s^2\), for \(\beta,p>0\). No explicit Lean theorem identifying the paper’s \(S\) is supplied; this is a valid external dictionary, not a separately displayed formal bridge.

- **Zero-phase regression — correct.** Since
  \[
  J_{2\lambda}(0)=\tfrac12\Gamma(\lambda)\beta^{-\lambda},
  \]
  the coefficient is \(2^{m-1}\mathrm{amplitudeCoeff}\). Returning to \(n=N^2\) recovers
  \(\Gamma(\lambda)\beta^{-\lambda}a_{-m}/(m-1)!\).
  This is the \(\beta\)-scaled version of the paper’s stated bare coefficient; at \(\beta=1\), it agrees literally.

### 2. Tail lemmas

**All stated bounds are correct.**

- The exponential remainder estimate includes \(J=0\).
- The even-power Gaussian estimate actually holds for **all real \(s\)**; its docstring unnecessarily says \(s\ge0\).
- Completing the square gives the stated Gaussian domination.
- For the documented `tailCoeff`,
  \[
  0\le\mathrm{tailCoeff}_{\beta,b}(K)
  \le e^{b^2/(2\beta)}
       \frac{(4b^2/\beta)^K}{K!}\longrightarrow0.
  \]
- `phase_tail_le` follows by allocating \(\beta/2\) to linear-exponential domination, then \(\beta/4\) to absorbing \(s^{2K}\), leaving the stated \(\beta/4\) Gaussian envelope. Its hypothesis \(|x|\le b\) already implies \(b\ge0\).
- `phaseMoment_taylor_le` correctly requires **\(|\beta a|\le b\)** and includes the Gaussian moment’s factor \(1/2\). Its envelope is finite:
  \[
  \mathrm{gaussTail}_{\beta,p}
  =\tfrac12\Gamma(p/2)(\beta/4)^{-p/2}.
  \]
- The finite-\(N\) and face-side remainder statements have the appropriate amplitude bound and normalisation. No missing positivity assumption on \(\eta\) is needed.

### 3. Mirror prose and scope

The mirror’s displayed formulas and \(J/S\) dictionary are faithful. Replacing \((0,1]^d\) by \([0,1]^d\) is harmless for these Lebesgue integrals.

The claimed recovery is **of the leading Taylor-tree coefficient**, not the full Taylor-tree expansion, a remainder rate, chart assembly, or a posterior theorem. The mirror appropriately limits its scope.

Two qualifications should remain explicit:

- These are fixed-phase limits, not uniform limits over families of phases.
- Signed amplitudes can make the coefficient zero. The theorem then gives a zero normalised limit, not identification of the first nonzero asymptotic term or an asymptotic equivalence.

### 4. Numerical sanity checks

Take \(\beta=1\), \(k_1=k_2=1\), \(\eta=1\).

- **Mixed:** \(h_1=0,h_2=1\), so \(p_1=1,p_2=2\):
  \[
  \sqrt n\,I_n\to\sqrt\pi/2\approx0.886227,
  \qquad \mathrm{noLogConst}(1,0,1,2)=\sqrt\pi/2.
  \]
- **Equal:** \(h_1=h_2=0\), zero phase:
  \[
  \frac{I_N}{N^{-1}\log N}\to\sqrt\pi/2.
  \]
  In \(n=N^2\), the coefficient is instead \(\sqrt\pi/4\), exactly the bare \(a_{-2}=1/4\) formula.

### 5. Should-fix versus cosmetic

**Should-fix**
1. Replace documentation expressions such as  
   `phaseMoment = S^{(β)}_{p/2}` and Taylor-error `|S(a) − …|` by \(J_p^{(\beta)}\) or `phaseMoment`. Even with the parenthetical explanation, reusing \(S\) invites a factor-of-two error.
2. If not already explicit immediately upstream, state the mirror’s standing assumptions: \(d\ge1\), \(h_i\in\mathbb N\), \(k_i>0\), \(\beta>0\), and \(\lambda\) the attained minimum.

**Cosmetic**
- Remove duplicated module-documentation fragments.
- Distinguish the Lean parameter `m` (dimension minus one) from prose multiplicity \(m=|J|\).
- Make the Taylor prefactor \((\beta N)^j/j!\) explicit.
- Clarify the swapped headline’s ambiguous “dominated coordinate” wording.
