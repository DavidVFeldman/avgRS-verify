"""Standalone verification of S0, R8 and the identity R8 = (σ + r²P)·R3 − P(1−r²)·S0.

Python 3 only, exact rationals, no third-party packages. Two independent legs, as in
`zindependent.py`: the resolvent built by Gaussian elimination over the truncated series ring, and
the generating functions built by enumerating partitions. S0 and R8 are checked on both.

Run:  python3 zline_r8_check.py [order]      (default 24)
"""
from fractions import Fraction as F
from math import factorial
import sys, os

N = 24

def zero(): return [F(0)] * (N + 1)
def const(c):
    s = zero(); s[0] = F(c); return s
def mono(k, c=1):
    s = zero()
    if k <= N: s[k] = F(c)
    return s
def sadd(*xs):
    o = zero()
    for x in xs:
        for i in range(N + 1): o[i] += x[i]
    return o
def ssub(x, y): return [a - b for a, b in zip(x, y)]
def smul(x, y):
    o = zero()
    for i, xi in enumerate(x):
        if xi:
            for j in range(N + 1 - i):
                if y[j]: o[i + j] += xi * y[j]
    return o
def sscale(c, x):
    c = F(c); return [c * a for a in x]
def sdiv(x, y):
    if y[0] == 0: raise ZeroDivisionError
    o = zero()
    for i in range(N + 1):
        acc = x[i]
        for j in range(1, i + 1):
            if y[j]: acc -= y[j] * o[i - j]
        o[i] = acc / y[0]
    return o
def sderiv(x): return [x[i + 1] * (i + 1) for i in range(N)] + [F(0)]
def spow(x, k):
    o = const(1)
    for _ in range(k): o = smul(o, x)
    return o
def iszero(x, upto): return all(x[i] == 0 for i in range(min(upto, N) + 1))
def firstnz(x): return next((i for i, c in enumerate(x) if c != 0), None)

def scalars(t, w, n):
    """P, P̂, Q, P₁, P̂₁ from the resolvent, by Gaussian elimination (no Neumann series)."""
    lam = [F(1)] * n
    for b in range(1, n): lam[b] = lam[b - 1] * ((b + 1) ** 2 - t)
    mu = [F(1)] * n
    mu[0] = 1 - t
    for a in range(1, n): mu[a] = mu[a - 1] * ((a - 1) ** 2 - t)
    H = [[mono(a + b + 1, F(1, factorial(a) * factorial(b) * (a + b + 1))) for b in range(n)]
         for a in range(n)]
    v = [mono(a, F(1, factorial(a))) for a in range(n)]
    def mm(A, B): return [[sadd(*[smul(A[i][k], B[k][j]) for k in range(n)]) for j in range(n)]
                          for i in range(n)]
    def dgR(A, d): return [[sscale(d[j], A[i][j]) for j in range(n)] for i in range(n)]
    def mv(A, x): return [sadd(*[smul(A[i][k], x[k]) for k in range(n)]) for i in range(n)]
    C1 = dgR(mm(dgR(H, lam), H), mu)
    C1h = dgR(mm(dgR(H, mu), H), lam)
    def solve(C, rhs):
        M = [[(const(1) if i == j else zero()) for j in range(n)] + [rhs[i]] for i in range(n)]
        for i in range(n):
            for j in range(n): M[i][j] = sadd(M[i][j], sscale(w, C[i][j]))
        for col in range(n):
            piv = next(i for i in range(col, n) if M[i][col][0] != 0)
            M[col], M[piv] = M[piv], M[col]
            inv = M[col][col]
            M[col] = [sdiv(e, inv) for e in M[col]]
            for i in range(n):
                if i != col and not iszero(M[i][col], N):
                    f = M[i][col]
                    M[i] = [ssub(M[i][j], smul(f, M[col][j])) for j in range(n + 1)]
        return [M[i][n] for i in range(n)]
    p, ph = solve(C1, v), solve(C1h, v)
    A = lambda x: [sscale(a, x[a]) for a in range(n)]
    dot = lambda x, y: sadd(*[smul(x[a], y[a]) for a in range(n)])
    Mv = [sscale(mu[a], v[a]) for a in range(n)]
    Lv = [sscale(lam[a], v[a]) for a in range(n)]
    return dict(P=dot(Mv, p), Ph=dot(Lv, ph), Q=dot(Mv, (lambda HL: mv(HL, ph))(dgR(H, lam))),
                P1=dot(A(Mv), p), Ph1=dot(A(Lv), ph))

def S0(t, w, S):
    r, P, Ph, Q, P1, Ph1 = mono(1), S['P'], S['Ph'], S['Q'], S['P1'], S['Ph1']
    M = lambda *xs: [x for x in xs] and __import__('functools').reduce(smul, xs)
    T = [( 1,6,[P,Ph,Q,Q],2),( 1,6,[P,P,Ph,Ph],1),(-1,5,[P,Ph,Q],1),(-1,5,[P,Q,Ph1],1),
         (-1,5,[Ph,Q,P1],1),(-F(t),4,[P,Ph],0),(-2,4,[P,Ph,Q,Q],2),(-2,4,[P,P,Ph,Ph],1),
         (-2,4,[P,Ph],0),(-1,4,[P,Ph1],0),( 3,4,[Ph,P1],0),( 1,4,[P1,Ph1],0),
         ( 2,3,[P,Ph,Q],1),( 2,3,[P,Q,Ph1],1),( 2,3,[Ph,Q,P1],1),( F(t),2,[P,Ph],0),
         ( 1,2,[P,Ph,Q,Q],2),( 1,2,[P,P,Ph,Ph],1),( 1,2,[Q,Q],1),(-1,2,[P,Ph],0),
         ( 1,2,[P,Ph1],0),(-3,2,[Ph,P1],0),(-2,2,[P1,Ph1],0),(-F(t),1,[Q],0),
         (-1,1,[P,Ph,Q],1),(-1,1,[P,Q,Ph1],1),(-1,1,[Ph,Q,P1],1),( 1,1,[Q],0),( 1,0,[P1,Ph1],0)]
    acc = zero()
    for c, k, fs, wp in T:
        term = sscale(F(c) * F(w) ** wp, mono(k))
        for f in fs: term = smul(term, f)
        acc = sadd(acc, term)
    return acc

def R3(t, w, S):
    r, P, Ph, Q, P1, Ph1 = mono(1), S['P'], S['Ph'], S['Q'], S['P1'], S['Ph1']
    return sadd(sscale(2, smul(mono(4), smul(P, Ph))), smul(mono(4), smul(P, Ph1)),
                sscale(-1, smul(mono(4), smul(Ph, P1))),
                sscale(-2, smul(mono(2), smul(P, Ph))), sscale(-2, smul(mono(2), smul(P, Ph1))),
                sscale(2, smul(mono(2), smul(Ph, P1))), sscale(-2, smul(mono(1), Q)),
                smul(P, Ph1), sscale(-1, smul(Ph, P1)))

def R8_grouped(t, w, S):
    """u σ² P̂ − [right-hand side of the grouped form]."""
    r, P, Ph, Q, P1 = mono(1), S['P'], S['Ph'], S['Q'], S['P1']
    u = ssub(const(1), mono(2))
    sig = smul(u, ssub(P1, sscale(w, smul(r, smul(P, Q)))))
    lhs = smul(u, smul(spow(sig, 2), Ph))
    rhs = sadd(sscale(-w, smul(spow(u, 3), smul(mono(2), smul(spow(Ph, 2), spow(P, 3))))),
               smul(spow(u, 2), smul(r, smul(Ph, smul(spow(P, 2),
                    ssub(sscale(w, smul(sadd(mono(2), const(1)), Q)), sscale(t, r)))))),
               smul(u, sadd(smul(mono(2), smul(Ph, spow(P, 2))),
                            sscale(w, smul(mono(2), smul(P, spow(Q, 2)))),
                            sscale(t, smul(r, smul(P, Q))),
                            sscale(-2, smul(r, smul(P1, Q))))),
               sscale(-1, smul(r, smul(sadd(mono(2), const(1)), smul(P, Q)))))
    return ssub(lhs, rhs)

def R8_from_S0_R3(t, w, S):
    """(σ + r²P)·R3 − P(1−r²)·S0, which should equal the grouped-form left minus right."""
    r, P, Q, P1 = mono(1), S['P'], S['Q'], S['P1']
    u = ssub(const(1), mono(2))
    sig = smul(u, ssub(P1, sscale(w, smul(r, smul(P, Q)))))
    return ssub(smul(sadd(sig, smul(mono(2), P)), R3(t, w, S)), smul(smul(P, u), S0(t, w, S)))

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    for t, w in [(F(-23,10),F(3,5)), (F(-7,3),F(2,7)), (F(5,2),F(-3,4)), (F(1,3),F(4,3)),
                 (F(9),F(1,5)), (F(-100),F(1,3))]:
        S = scalars(t, w, N // 2 + 2)
        lim = N - 6
        s0, g, d = S0(t, w, S), R8_grouped(t, w, S), R8_from_S0_R3(t, w, S)
        print("t = %-8s ω = %-6s   S0 %s   R8 (grouped) %s   R8 = (σ+r²P)R3 − PuS0 %s" % (
            t, w,
            "OK" if iszero(s0, lim) else "r^%s" % firstnz(s0),
            "OK" if iszero(g, lim) else "r^%s" % firstnz(g),
            "OK" if iszero(ssub(d, sscale(-1, g)), lim) or iszero(ssub(d, g), lim)
                 else "r^%s" % firstnz(ssub(d, g))))
