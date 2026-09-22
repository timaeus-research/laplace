"""Tide frame-covariance: the note's tensor formulas are covariant under w = Q u + c for arbitrary symmetric tensors.
With H' = Q H Q^T, T'_ijk = sum Q_ia Q_jb Q_kc T_abc, Q4' likewise, S' = (t H')^{-1} = Q S Q^T:
  contractT T' S' = Q (contractT T S);  bubble T' S' = Q bubble Q^T;  tadpoleLine T' S' = Q tadpoleLine Q^T;  contractQ Q4' S' = Q contractQ Q^T;
  oneLoopCov' = Q oneLoopCov Q^T;  meanShift' = Q meanShift;  covKFormula(H',T',Q B Q^T, Q b) = covKFormula(H,T,B,b);  twoLoopEnergy' = twoLoopEnergy."""
import numpy as np
rng = np.random.default_rng(3); d = 4; t = 7.0
A = rng.normal(size=(d, d)); H = A @ A.T + d * np.eye(d)
T = rng.normal(size=(d, d, d)); T = (T + T.transpose(1,0,2) + T.transpose(0,2,1) + T.transpose(1,2,0) + T.transpose(2,0,1) + T.transpose(2,1,0)) / 6
Q4 = rng.normal(size=(d, d, d, d)); Q4 = sum(np.transpose(Q4, p) for p in __import__('itertools').permutations(range(4))) / 24
B = rng.normal(size=(d, d)); b = rng.normal(size=d)
Q, _ = np.linalg.qr(rng.normal(size=(d, d)))
def rotT(T): return np.einsum('ia,jb,kc,abc->ijk', Q, Q, Q, T)
def rotQ(Q4): return np.einsum('ia,jb,kc,ld,abcd->ijkl', Q, Q, Q, Q, Q4)
def contractT(T, S): return np.einsum('lmn,mn->l', T, S)
def contractQ(Q4, S): return np.einsum('ijkl,kl->ij', Q4, S)
def bubble(T, S): return np.einsum('ikl,km,ln,jmn->ij', T, S, S, T)
def tadpole(T, S): return np.einsum('ijk,kl,l->ij', T, S, contractT(T, S))
def oneLoopCov(H, T, Q4):
    S = np.linalg.inv(t * H); Pi = -(t / 2) * contractQ(Q4, S) + (t**2 / 2) * bubble(T, S) + (t**2 / 2) * tadpole(T, S); return S + S @ Pi @ S
def meanShift(H, T): S = np.linalg.inv(t * H); return -0.5 * S @ (t * contractT(T, S))
def covK(H, T, B, b):
    S = np.linalg.inv(t * H); TS = contractT(T, S); SHS = S @ H @ S
    return 0.5 * np.trace(H @ S @ B @ S) + 0.5 * (S @ b) @ TS - t / 2 * b @ (SHS @ TS) - t / 2 * (S @ b) @ contractT(T, SHS)
def twoLoop(H, T, Q4):
    S = np.linalg.inv(t * H); theta = np.einsum('ij,ij->', S, bubble(T, S)); TS = contractT(T, S)
    return 0.5 * np.trace(H @ S) + t / 12 * theta + t / 8 * TS @ (S @ TS) - np.einsum('ij,ij->', contractQ(Q4, S), S) / 8
Hp, Tp, Q4p = Q @ H @ Q.T, rotT(T), rotQ(Q4); S = np.linalg.inv(t * H); Sp = np.linalg.inv(t * Hp)
print("S' - Q S Q^T:", np.abs(Sp - Q @ S @ Q.T).max())
print("contractT:", np.abs(contractT(Tp, Sp) - Q @ contractT(T, S)).max(), " bubble:", np.abs(bubble(Tp, Sp) - Q @ bubble(T, S) @ Q.T).max(),
      " tadpole:", np.abs(tadpole(Tp, Sp) - Q @ tadpole(T, S) @ Q.T).max(), " contractQ:", np.abs(contractQ(Q4p, Sp) - Q @ contractQ(Q4, S) @ Q.T).max())
print("oneLoopCov:", np.abs(oneLoopCov(Hp, Tp, Q4p) - Q @ oneLoopCov(H, T, Q4) @ Q.T).max(), " meanShift:", np.abs(meanShift(Hp, Tp) - Q @ meanShift(H, T)).max())
print("covKFormula:", abs(covK(Hp, Tp, Q @ B @ Q.T, Q @ b) - covK(H, T, B, b)), " twoLoopEnergy:", abs(twoLoop(Hp, Tp, Q4p) - twoLoop(H, T, Q4)))
# non-symmetric T: does covariance still hold? (it should: the identities are index gymnastics, no symmetry used)
Tn = rng.normal(size=(d, d, d)); Q4n = rng.normal(size=(d, d, d, d))
print("non-symmetric tensors: oneLoopCov", np.abs(oneLoopCov(Hp, rotT(Tn), rotQ(Q4n)) - Q @ oneLoopCov(H, Tn, Q4n) @ Q.T).max(), " twoLoop", abs(twoLoop(Hp, rotT(Tn), rotQ(Q4n)) - twoLoop(H, Tn, Q4n)), " covK", abs(covK(Hp, rotT(Tn), Q @ B @ Q.T, Q @ b) - covK(H, Tn, B, b)))
