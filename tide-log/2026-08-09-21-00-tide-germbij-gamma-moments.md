# Tide: germbij-gamma-moments (stage 3 of the gamma-rung programme)

**Direction (user):** gamma-rung programme stage 3: the second-order
Gibbs moment rates feeding the kappa4 assembly.

**Seabed:** laplace, main at 5478582 (stage 2 complete:
J_n_asymptotic_order2 with the A^2/(2t) coefficient at error
K/(t sqrt t)). Mirror source for the ratio-with-rates technique:
mean_anharmonic_O2_rate (IntegralRemainder.lean).
**Worktree/branch:** laplace-tide-germbij-gamma-moments /
tide/germbij-gamma-moments
**Started:** 2026-08-09T21:00Z

## Candidates (programme-inherited, scoping consult 1(b) minimal path)

With A = cubicScale, B = quarticScale:
- secondMoment_anharmonic_order2_rate:
  |t<x^2> - 1/lam - ((45A^2-12B)/lam)/t| <= K/(t sqrt t), t >= T.
- fourthMoment_anharmonic_order2_rate:
  |t^2<x^4> - 3/lam^2 - ((450A^2-96B)/lam^2)/t| <= K/(t sqrt t).
- thirdMoment_anharmonic_rate: |t^2<x^3> + 15A/lam^(3/2)| <= K/sqrt(t)
  (leading only; first-order J_n machinery suffices since m_3 = m_7 = 0).
Structural facts: J_0 has no 1/sqrt(t) term; g-ratios m_4/m_0 = 3,
m_6/m_0 = 15, m_8/m_0 = 105, m_10/m_0 = 945.

## Numerical check

Run before any Lean (scipy, (1.3, 0.4, 0.9)):
t=200: t(t<x2>-1/l) = -0.13477 vs C2 = -0.13480;
t(t2<x4>-3/l2) = -0.72239 vs C4 = -0.72180;
t2<x3> = -0.45265 -> target -0.45517. All three confirmed
(t=800 rows show the known float-cancellation collapse; archived in
/tmp shell transcript and quoted here).

## Execution plan (handoff-grade)

File Laplace/OneD/MomentSecondOrder.lean, three layers:

1. BRIDGES (mirror private mean_J_form_exact at IntegralRemainder:1598,
   via I_n_J_n_relation :793; the sl/st set + field_simp endgame):
   - secondMoment_J_form_exact: t * <x^2> = J_2/(lam * J_0)
     [(sqrt(lam t))^3 I_2 = J_2; t<x^2> = t I_2/Z = J_2/(lam J_0)]
   - thirdMoment_J_form_exact: t^2 * <x^3> = sqrt t * J_3/(lam^(3/2)... 
     use (sqrt lam)^3 to stay radical-atom: = sqrt t * J_3 /
     ((Real.sqrt lam)^3 * J_0)
   - fourthMoment_J_form_exact: t^2 * <x^4> = J_4/(lam^2 * J_0)

2. DELTAS (specialize J_n_asymptotic_order2 at n = 0, 2, 4 and
   J_n_asymptotic at n = 3; kill odd moments via
   integral_pow_mul_exp_neg_sq_odd, evaluate even ones via
   integral_pow_mul_exp_neg_sq_half: m_{2k} = (2k-1)!! sqrt(2pi):
   m_0 = c, m_2 = c, m_4 = 3c, m_6 = 15c, m_8 = 105c, m_10 = 945c,
   c := sqrt(2pi)):
   - hd0: |J_0 - c - (15A^2/2 - 3B) c / t| <= K_0/(t sqrt t)
   - hd2: |J_2 - c - (105A^2/2 - 15B) c / t| <= K_2/(t sqrt t)
   - hd4: |J_4 - 3c - (945A^2/2 - 105B*... careful: n=4 coeffs:
     -B m_8 + A^2/2 m_10 = (-105B + 945A^2/2) c| <= K_4/(t sqrt t)
   - hd3: |J_3 + A m_6/sqrt t| = |J_3 + 15 A c/sqrt t| <= K_3/t
     (from first-order J_n_asymptotic at n = 3: m_3 = m_7 = 0)

3. ASSEMBLIES (the c2-cancellation pattern; J_0_eventually_bounded for
   the denominator, J_0 >= c/2 form — check its exact statement):
   - t<x^2> - 1/lam - C2/(lam... statement C2 := (45A^2-12B)/lam:
     numerator N := J_2 - (1 + (45A^2-12B)/t) * J_0; algebra:
     N = [P_2 - (1+c2/t)P_0] + e_2 - (1+c2/t)e_0 with
     P_k = c(1+q_k/t), q_0 = 15A^2/2-3B, q_2 = 105A^2/2-15B,
     c2 = q_2 - q_0 = 45A^2-12B EXACT -> P-part = -c*c2*q_0/t^2;
     |N| <= c|c2 q_0|/t^2 + K_2/(t sqrt t) + (1+|c2|/t)K_0/(t sqrt t)
     and t^2 >= t sqrt t, 1/t <= 1 for t >= 1.
     Then |t<x^2> - 1/lam - C2/t| = |N|/(lam J_0) <= 2|N|-bound/(lam c).
   - same for x^4 with c4 = q_4 - 3 q_0 (q_4 := (945A^2/2 - 105B)/3?
     CAREFUL: J_4 = 3c(1 + q_4/t) with 3c q_4 = (945A^2/2-105B)c i.e.
     q_4 = (315A^2/2 - 35B); target coeff c4 := q_4 - q_0*... numerator
     N4 = J_4 - (3 + c4'/t) J_0 with c4' = lam^2 C4 = 450A^2-96B;
     check: 3(1+q_4/t) - (3+c4'/t)(1+q_0/t): 1/t coeff: 3q_4 - c4' - 3q_0
     = (945/2 - 45/2)A^2 - (105-9)B - c4' = 450A^2 - 96B - c4' = 0 ✓.
   - x^3: numerator N3 := sqrt t J_3 + 15A/... target
     |t^2<x^3> + 15A/(sqrt lam)^3| <= K/sqrt t: N3 = sqrt t J_3 + 15Ac...
     t^2<x^3> - (-15A c/(c... : sqrt t J_3/((sl)^3 J_0) + 15A/(sl)^3
     = (sqrt t J_3 + 15A J_0)/((sl)^3 J_0); sqrt t J_3 = -15Ac + sqrt t e_3
     with |e_3| <= K_3/t so |sqrt t e_3| <= K_3/sqrt t; and
     15A(J_0 - c) : |J_0 - c| <= K_0'/t (first-order J_0 delta suffices);
     |N3| <= K_3/sqrt t + 15|A| K_0'/t <= K'/sqrt t.

Numerical check: done (see above). Deliberation: programme-inherited.

## Result

- Branch tide/germbij-gamma-moments,
  Laplace/OneD/MomentSecondOrder.lean (ten declarations): three private
  J-form bridges (t<x^2> = J_2/(lam J_0) and the x^3/x^4 analogues, via
  I_n_J_n_relation with radical-atom endgames); four private deltas
  (J_0, J_2, J_4 at second order and J_3 at first, Gaussian constants
  evaluated: 1, 3, 15, 105, 945 times sqrt(2pi), odd moments killed);
  and the three public rates: secondMoment_anharmonic_order2_rate
  (coefficient (45A^2-12B)/lam), fourthMoment_anharmonic_order2_rate
  ((450A^2-96B)/lam^2), thirdMoment_anharmonic_rate (leading
  -15A/sqrt(lam)^3 at K/sqrt(t)). Also de-privatised
  J_0_eventually_bounded on second use.
- Built across four checkpointed WIP commits (bridges / deltas / first
  assembly / remaining two). The deltas built FIRST TRY. Iterations, all
  catalogue classes: dead tactics after field_simp/gcongr; div_le_div_iff
  and le_div_iff are now the ₀-variants; set_option must precede the
  docstring, not sit between it and the theorem; and one instance of the
  unsafe t-inside-radical rewrite (my own CLAUDE.md warning) caught by
  the goal display and fixed with the radical-atom pattern.
- The exact 1/t cancellations (q_2 - q_0 = c_2; p_4 - 3q_0 = c_4') were
  verified by ring on explicit coefficients, as planned.

## Vote

Programme-inherited (scoping consult 1(b) minimal path); execution
followed the logged handoff plan without deviation.
