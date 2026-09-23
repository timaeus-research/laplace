**Vote: approve A–C.** Add the exact finite-\(n\) correction and its upper bound; monotonicity is also cheap. One interpretation needs reversing.

### 1. Correctness and side conditions

**A is correct.** For integer \(n\ge0\) and \(z\ne1\),
\[
\sum_{k=1}^{n}(n-k)z^k
=\frac{nz}{1-z}-\frac{z(1-z^n)}{(1-z)^2}.
\]
The \(k=n\) term is zero, so this is precisely your lag sum. Consequently, for **\(n\ge1\)**,
\[
F_n(z)=\frac{1+z}{n(1-z)}
-\frac{2z(1-z^n)}{n^2(1-z)^2}.
\]
At \(z=1\), the original definition instead gives \(F_n(1)=1\).

**B is correct** for every fixed \(0\le z<1\):
\[
nF_n(z)\longrightarrow\frac{1+z}{1-z}.
\]

**C is correct**, assuming a finite spectrum and the strict stability conditions
\[
0<\eta\lambda_i<2.
\]
These give \(a_i>0\), \(z_i:=\alpha_i^2<1\), and
\[
1-\alpha_i^2=2\eta\lambda_i a_i.
\]
Thus
\[
\frac12\sum_i a_i^{-2}\frac{1+\alpha_i^2}{1-\alpha_i^2}
=\sum_i\frac{1+\alpha_i^2}{4\eta\lambda_i a_i^3}
=L_\eta,
\qquad
nW_{\eta,n}\longrightarrow L_\eta.
\]

### 2. Cheap strengthenings

The most useful package is the **exact deficit and rate**:
\[
0\le \frac{1+z}{1-z}-nF_n(z)
=\frac{2z(1-z^n)}{n(1-z)^2}
\le\frac{2z}{n(1-z)^2}.
\]
Summing gives
\[
0\le L_\eta-nW_{\eta,n}
=\frac1n\sum_i
\frac{a_i^{-2}z_i(1-z_i^n)}{(1-z_i)^2}
\le\frac{D_\eta}{n},
\quad
D_\eta:=\sum_i\frac{a_i^{-2}z_i}{(1-z_i)^2}.
\]
In particular, \(W_{\eta,n}=L_\eta/n+O(n^{-2})\), with a nonpositive correction.

**Monotonicity is also easy:**
\[
(n+1)F_{n+1}(z)-nF_n(z)
=\frac{2}{n(n+1)}\sum_{k=1}^{n}kz^k\ge0.
\]
Hence \(nW_{\eta,n}\uparrow L_\eta\). The scalar increase is strict for \(z>0\); the summed increase is strict if some \(\alpha_i\ne0\).

**Wording correction:** \(nW_{\eta,n}\le L_\eta\) does **not** mean the fixed-\(n\) average “never beats the long-run rate.” Rather, its variance is **at most the long-run approximation \(L_\eta/n\)**: the normalized variance approaches the long-run constant **from below**.

### 3. Suggested one-line note

> For fixed strictly stable \(\eta\), the limiting fixed-window variance recovers tide 103’s long-run variance as \(nW_{\eta,n}\uparrow L_\eta\), with deficit \(O(n^{-1})\); this is a sequential limit after the anchored post-burn-in limit, not an assertion of limit interchange or uniformity near the stability boundaries.

**Closing-tide recommendation:** land A–C plus the exact deficit bound; include monotonicity if its short proof fits.