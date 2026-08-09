# Tide: germbij-jet-difference (weighted-jet programme, stages 3A-3C)

**Direction (user):** the pairwise-difference route to the §7.4
recovery theorem (auto mode, standing delegation): exponential secant
lemma, min-ρ common envelope, and the dominated-convergence limit
q^{-r}(J_s^1 − J_s^2) → −δ_r·A_{s+2k+r} over 𝓝[>] 0.

**Seabed:** laplace, main at da55784 (stage 2 merged).
**Worktree/branch:** laplace-tide-germbij-jet-difference /
tide/germbij-jet-difference
**Started:** 2026-08-10T03:15Z

## Route deliberation

Consult saved verbatim: `tide-log/gpt56_jet_difference_route_v1.md`.
The consult's original stages 3-5 (multi-index coefficient polynomials
P_n, triangular decomposition, quotient recurrence) were challenged
with a pairwise-difference alternative: recovery is a comparison
statement, so per rung one needs only the FIRST-order difference of
two Gibbs weights, not the full expansion of each. GPT endorses the
alternative ("mathematically sound, and the shortest route"), with two
refinements adopted verbatim:
- Use the exponential secant estimate |e^{-x} − e^{-y}| ≤
  |x−y|·max(e^{-x}, e^{-y}) rather than the drafted e^{|D|} Taylor
  bound, which is NOT controlled by the endpoint envelopes.
- ρ = min(ρ₁, ρ₂) works for both jets and the whole segment between
  them; no mixed-jet construction.
Replaces stages 3-5 with 3A-3G; this tide is 3A-3C, with 3C
(parameterized dominated convergence over 𝓝[>] 0) named the most
likely bottleneck and deliberately isolated as a reusable theorem.

## Vote

- Claude: pairwise-difference route, this tide = 3A-3C ending at
  q^{-r}(J_s^1 − J_s^2) → −δ_r A_{s+2k+r}.
- GPT-5.6 Sol: same ("recommend (b), refined as a generic pairwise
  linear-response lemma").

Agreed.

## Numerical check

Executed before the consult returned (scipy, k = 1, a = 1, jets
(0.3, 0.5) vs (0.1, 0.5) differing at rung r = 1): the normalized
version q^{-1}(F_s^1 − F_s^2) → −δ_1·Cov(u^s, u^3): measured/predicted
ratios 0.9999 at q = 0.005 for s = 1 (−0.149988 vs −0.15) and s = 3
(−0.374946 vs −0.375); for s = 2 the q^1 coefficient vanishes by
parity exactly as predicted (Cov(u², u³) = 0), confirming the
consult's warning that the data must include the matching moment
s = 2k+r. The unnormalized 3C limit is the same computation before
the quotient rule.

## Planned declarations

exp_secant_le (|e^{-x} − e^{-y}| ≤ |x−y| max);
jetPotential_lower_bound_min (min-ρ envelope);
integrable_abs_pow_mul_exp_neg_kth + the summed majorant;
jetPotential_zero (q = 0 collapse to the reference);
jet_difference_pointwise (the q → 0⁺ pointwise limit via
e^{-L¹} − e^{-L²} = e^{-L²}(e^{-D} − 1), e^{-D} − 1 = −D +
expRemainder 2 D, |expRemainder 2 D| ≤ |D|²/2·max(1, e^{-D}) from the
seabed's ExpRemainderSigned, and the polynomial factorization
D_q = q^r·g(q) with g continuous, g(0) = δ_r u^{2k+r});
jet_difference_integral_limit (3C: DCT via
tendsto_integral_filter_of_dominated_convergence over 𝓝[>] 0,
majorant q-free on Ioc 0 1).
Indexing: rung r = i₀.1 + 1 for i₀ : Fin R; hlow : ∀ j < i₀,
c¹ j = c² j.

## Result

- Declarations (Laplace/OneD/JetDifference.lean, ~415 lines, zero
  sorries, zero warnings): exp_secant_le (+ private one-sided case),
  exp_sub_one_eq (e^{-s} − 1 = −s + expRemainder 2 s),
  jetPotential_zero, jetPotential_continuous_q,
  jetPotential_lower_bound_min, integrable_abs_pow_mul_exp_neg_kth,
  jet_difference_factor (D_q = q^r·g(q) with per-term Fin case
  analysis), jet_difference_pointwise (the q → 0⁺ limit via
  Finset.sum_eq_single evaluation of g(0), squeeze of the
  second-order remainder against q^r·|g|²/2·max(1, e^{-D}), and
  Tendsto.congr' on the eventual identity), and the stage-3C core
  jet_difference_integral_limit (DCT via
  tendsto_integral_filter_of_dominated_convergence over 𝓝[>] 0 with
  the q-free majorant Σ_j |δ_j|·|u|^{s+2k+j+1}·e^{-ρu^{2k}} on
  Ioc 0 1).
- The predicted bottleneck (3C's parameterized DCT) went through
  first try once the calc used gcongr for the division-monotone
  steps; the majorant algebra needed one extra calc step separating
  the q^r cancellation (field_simp; ring) from the sum reshaping
  (Finset.sum_mul + Finset.mul_sum + pow_add per term).
- Surprises: (1) the initial draft misused the q-continuity lemma
  where u-continuity was needed in the measurability bullet — caught
  at first build; (2) Tendsto.const_mul + Tendsto.congr (fun q ↦ by
  ring) is a clean two-line bridge from the pointwise lemma to the
  DCT's per-u limit shape; (3) Fin index arithmetic (j.1 − i₀.1 with
  ℕ-subtraction) is harmless exactly because the j < i₀ terms carry
  δ_j = 0, so both sides of the factorization vanish there regardless
  of the truncated exponent.
