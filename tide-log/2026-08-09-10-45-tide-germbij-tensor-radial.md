# Tide: germbij tensor programme J4 (degree-k radial Taylor)

**Direction (user):** standing auto-mode commission on the germbij
note; stage J4 per the archived tensor scoping consult (in the J2
tide log dir: gpt56_tensor_scoping_v1.md).
**Seabed:** laplace main at c3d1747 (J2 merged; J3 in PR #75,
independent code — this tide branches off main in parallel).
**Started:** 2026-08-09T10:45 local

## Candidates

Consult J4, in the pairwise form it recommends ("it is often cleaner
to compare two losses whose derivatives agree below k"):

1. `taylorHomogeneousTerm k L x := (k!)⁻¹ · iteratedFDeriv ℝ k L 0
   (fun _ ↦ x)` (the diagonal Taylor term).
2. `ray_iteratedDeriv`: iteratedDeriv m (fun t ↦ L (t•x)) 0 =
   iteratedFDeriv ℝ m L 0 (fun _ ↦ x) for m ≤ n, ContDiff n L —
   NOT by per-order chain rule (H3a's route): by
   `ContinuousLinearMap.iteratedFDeriv_comp_right` composed with
   `iteratedDeriv_eq_iteratedFDeriv` and the toSpanSingleton ray.
   One line per order, all orders at once.
3. `pairwise_rescaled_loss_tendsto`: for C^k losses with equal
   iterated derivatives at 0 below order k (0 < k),
   Tendsto (fun q ↦ (L₁(q•x) − L₂(q•x))/q^k) (𝓝[>] 0)
     (𝓝 (taylorHomogeneousTerm k L₁ x − taylorHomogeneousTerm k L₂ x))
   via taylor_isLittleO on the ray of the difference: all Taylor
   terms below k vanish by the jet hypothesis, the k-th is the
   homogeneous difference, and the H3a division/assembly pattern
   finishes. (The j = 0 case of the hypothesis gives L₁ 0 = L₂ 0, so
   the plain difference form is equivalent to the base-subtracted
   one.)

Consult notes honored: the ray route rather than a multivariate
Taylor theorem ("substantially easier... naturally produces the
diagonal derivative, which is exactly what the covariance argument
needs"); the cautioned taylor_peano_diag indexing question does not
arise.

## Numerical check

Executed before this log was written (d=2, k=3: L₁ = quadratic +
cubic₁ + quartic₁, L₂ = same quadratic + cubic₂, shared jets below 3).
Output quoted verbatim below after execution.

## Vote

- Claude: J4 as staged (the consult's own pairwise form).
- GPT-5.6 Sol: same (archived scoping consult, section J4).

Agreed.
Delta_3(x) = 0.5632000000
q=0.1: (L1-L2)(qx)/q^3 = 0.5754880000  diff = 1.23e-02
q=0.01: (L1-L2)(qx)/q^3 = 0.5644288000  diff = 1.23e-03
q=0.001: (L1-L2)(qx)/q^3 = 0.5633228800  diff = 1.23e-04
