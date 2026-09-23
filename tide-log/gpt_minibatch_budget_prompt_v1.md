# Tide 101 consult: minibatch gradient noise in the E2–E4 error budget (laplace seabed, Lean 4 + Mathlib; E8)

Landed: E8 material — `minibatchNoise h t C = 2h·1 + h²t²·C`, the Lyapunov solution `lyapunovVia U ρ N` of `X = AXAᵀ + N` for `A = U diag(ρ) Uᵀ` with entries `(UᵀXU)ᵢⱼ = (UᵀNU)ᵢⱼ/(1 − ρᵢρⱼ)` (`lyapunovVia_conj_apply`, any orthogonal `U`), `minibatch_fixed_iff` (uniqueness), `minibatchCov_conj_diag`: `(UᵀΣU)ᵢᵢ = (1 + h t² Ĉᵢᵢ/2)/(pᵢκᵢ)` in the `orthoOf` frame, the finite-population-correction constants (`fpc_bilinear`, `minibatch_gradient_cov`), and the exact one-step SGLD recursion on linear regression (`sgld_law_step`: the "full law" with the state-dependent Hessian term). Tides 99–100: the E2–E4 budget `t⟨L∘A⟩_loc − t⟨½uᵀHu⟩_k = C₁′/t − (th/4)∑λᵢ/κᵢ + Burn_k + O(t⁻²)` and its stationary form; frame-general burn-in algebra.

Candidates v1 (Claude), with `pᵢ = tλᵢ + g`, `κᵢ = 1 − hpᵢ/2`, `ρᵢ = 1 − hpᵢ`, `Ĉ = UᵀCU`, constant (state-independent) gradient-noise covariance `C`:
A (Sampler, frame-general). `minibatchCov_frame_apply/diag`: `(UᵀΣ^{mb}U)ᵢⱼ = (2h[i=j] + h²t²Ĉᵢⱼ)/(1 − ρᵢρⱼ)`, diagonal `(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ)`, for `Σ^{mb} = lyapunovVia U ρ (minibatchNoise h t C)`, any `U` with `UᵀU = 1`, `UᵀPU = diag p`.
B (Sampler). The stationary energy trace for `H` in the same frame: `(t/2)·tr(H Σ^{mb}) = (t/2)∑ᵢλᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ)` — only the frame *diagonal* of `C` enters the LLC statistic's mean.
C (Multi, extended stationary budget). With the anchored mean unchanged by additive noise (`t·½mᵀHm = (t/2)∑λᵢbᵢ²`):
  `t⟨L∘A⟩_loc − [(t/2)∑λᵢ(1 + ht²Ĉᵢᵢ/2)/(pᵢκᵢ) + (t/2)∑λᵢbᵢ²] = C₁′/t − (th/4)∑ᵢλᵢ/κᵢ − (ht³/4)∑ᵢλᵢĈᵢᵢ/(pᵢκᵢ) + O(t⁻²)` (tide 95's constants): the minibatch term is a third bias, `−(ht³/4)∑λᵢĈᵢᵢ/(pᵢκᵢ) ≈ −(ht²/4)∑Ĉᵢᵢ/κᵢ` for `pᵢ ≈ tλᵢ`, i.e. with `h = η/t` it is `≈ −(ηt/4)tr Ĉ` — growing linearly in `t` unless `C = O(1/t)`.

Numerical check (E2 frame 2D, random PSD `C`, `h = 0.3/t`): the iterated Lyapunov fixed point matches the entry formula and the diagonal formula to 1e-16; `t(t⟨L⟩ − stationary + disc + mb)` → `C₁′` (−0.253 at t = 40 → −0.2716 at t = 640 vs −0.2729); the minibatch bias grows from 0.33 (t = 40) to 5.3 (t = 640).

Questions:
1. Are A–C correct? Is it right that only the frame diagonal of `C` enters the mean of the quadratic statistic (and the full `Ĉ` enters its variance)?
2. E8 reading: the note's `C = C_g = (1/m)(1 − m/n)S²` is the per-unit-`t²` gradient-noise covariance (the SGLD gradient is `t∇L`), so `h²t²C` is the injected noise; with `h = η/t` the extra LLC bias is `≈ (η/4)·t·tr(Ĉ)/κ` — is that the note's E8 statement ("minibatch noise inflates the LLC estimate by an amount growing with `t` unless the batch is enlarged with `t`")? How should the note phrase the three sampler biases (discretisation `(η/4)∑λᵢ/κᵢ`, minibatch `(ηt/4)∑Ĉᵢᵢ/κᵢ`, burn-in) against the anharmonic `C₁′/t`? Is the "full law" state-dependent term (Hessian fluctuation) needed for the mean of the energy, or is the constant-`C` law the right first approximation there?
3. Lean route: A by copying `minibatchCov_conj_apply/diag` with a general frame; B via `trace(H X) = trace(Dλ (UᵀXU))` (`trace_mul_comm`, `Matrix.mul_diagonal`) plus A's diagonal; C from tide 100's `ulaAnchored_llc_budget_stationary` and the per-mode identity `(1 + x)/y = 1/y + x/y`. Pitfalls?
4. Cheap additions (e.g. the variance under the minibatch law `½tr((HΣ^{mb})²) + (Hm)ᵀΣ^{mb}(Hm)` — needs off-diagonal `Ĉᵢⱼ`; the `h = η/t` scaling statement)?
5. Vote.
