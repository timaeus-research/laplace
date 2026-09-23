import numpy as np
def Fn(n, z): return (n + 2 * sum((n - (j + 1)) * z ** (j + 1) for j in range(n))) / n**2
def Fn_closed(n, z): return (1 + z) / (n * (1 - z)) - 2 * z * (1 - z**n) / (n**2 * (1 - z)**2)
lam = np.array([1.0, 2.5, 0.7]); eta = 0.3; a = 1 - eta * lam / 2; al = 1 - eta * lam
Leta = np.sum((1 + al**2) / (4 * eta * lam * a**3))
print("identity check |F_n - closed| :", max(abs(Fn(n, z) - Fn_closed(n, z)) for n in range(1, 12) for z in [0.0, 0.1, 0.5, 0.9, 0.99]))
print("L_eta (tide 103) =", Leta, " ½∑a⁻²(1+α²)/(1−α²) =", 0.5 * np.sum(a**-2 * (1 + al**2) / (1 - al**2)))
for n in [1, 5, 20, 100, 1000, 10000]:
    W = 0.5 * np.sum(a**-2 * np.array([Fn_closed(n, z) for z in al**2]))
    print(f"  n={n:6d}  n*W_n = {n * W:.6f}   n*F_n(0.5) = {n * Fn_closed(n, 0.5):.6f} -> {(1 + 0.5) / (1 - 0.5)}")
