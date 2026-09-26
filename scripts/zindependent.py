"""Independent recomputation of the z-line first integrals and closed forms.

Deliberately shares no code with the discovery pipeline (`zform2.py`, `zmodeng.py`, `zcheck_all.py`,
`zideal.py`, `zproof.py`), which all rest on python-flint series and, for the matrix objects, on a
Neumann series for the resolvent. Here:

  * arithmetic is pure Python `fractions.Fraction`; no flint, no sympy, no numpy;
  * the resolvent is obtained by Gaussian elimination over the truncated series ring, not by
    summing a Neumann series;
  * a second, wholly disjoint leg computes the generating functions by enumerating partitions and
    evaluating hook lengths and contents, with no matrices at all.

The two legs meet at the scalars P, Q, P̂, which the matrix leg produces from the resolvent and the
partition leg from ratios of generating functions. R6 and R7 are then evaluated on both.

  G₀ = Σ_λ ω^{d(λ)} w_t(λ) q^{|λ|},  G₁ = Σ_λ ω^{N₁(λ)} …,  Ĝ₁ = Σ_λ ω^{N̂₁(λ)} …,
  G₂ = Σ_λ ω^{N₂(λ)} …,   w_t(λ) = ∏_□ ((c(□)−1)² − t) / H_λ²,   q = r²,

with d the Durfee side, N₁ = #{i : a_i ≥ 1}, N₂ = #{i : a_i ≥ 2}, N̂₁ = #{i : b_i ≥ 1} in Frobenius
coordinates (a_i | b_i).

R7 is read from `zR7_terms.txt` as a list of exponent tuples, so no symbolic algebra system takes
part in the evaluation.

Usage:  python3 zindependent.py [order] ;  default 24 (partitions up to |λ| = order/2 + 1).
"""
from fractions import Fraction as F
from math import factorial
import sys, os

# ----------------------------------------------------------------- series ---
N = 24                                    # truncation: series in r modulo r^(N+1)

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
def sneg(x): return [-a for a in x]
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
    """x / y, requires y[0] != 0."""
    if y[0] == 0: raise ZeroDivisionError("series division by a non-unit")
    o = zero()
    for i in range(N + 1):
        acc = x[i]
        for j in range(1, i + 1):
            if y[j]: acc -= y[j] * o[i - j]
        o[i] = acc / y[0]
    return o
def sderiv(x): return [x[i + 1] * (i + 1) for i in range(N)] + [F(0)]
def sdiv_shift(x, y):
    """x / y when both have positive valuation: strip the common power of r first.
    The quotient is then reliable to order N − val(y)."""
    vy = next((i for i, c in enumerate(y) if c != 0), None)
    if vy is None: raise ZeroDivisionError
    xs = x[vy:] + [F(0)] * vy
    ys = y[vy:] + [F(0)] * vy
    return sdiv(xs, ys)
def spow(x, k):
    o = const(1)
    for _ in range(k): o = smul(o, x)
    return o
def iszero(x, upto=None):
    upto = N if upto is None else min(upto, N)
    return all(x[i] == 0 for i in range(upto + 1))
def firstnz(x):
    return next((i for i, c in enumerate(x) if c != 0), None)

# ------------------------------------------------------- leg A: matrices ----
def matrix_leg(t, w, n):
    """Resolvent by Gaussian elimination over the series ring. Returns the scalar dictionary."""
    lam = [F(1)] * n
    for b in range(1, n): lam[b] = lam[b - 1] * ((b + 1) ** 2 - t)
    mu = [F(1)] * n
    mu[0] = 1 - t
    for a in range(1, n): mu[a] = mu[a - 1] * ((a - 1) ** 2 - t)
    H = [[mono(a + b + 1, F(1, factorial(a) * factorial(b) * (a + b + 1))) for b in range(n)]
         for a in range(n)]
    v = [mono(a, F(1, factorial(a))) for a in range(n)]

    def matmul(A, B):
        return [[sadd(*[smul(A[i][k], B[k][j]) for k in range(n)]) for j in range(n)]
                for i in range(n)]
    def dgmul_left(d, B):  return [[sscale(d[i], B[i][j]) for j in range(n)] for i in range(n)]
    def dgmul_right(A, d): return [[sscale(d[j], A[i][j]) for j in range(n)] for i in range(n)]
    def matvec(A, x): return [sadd(*[smul(A[i][k], x[k]) for k in range(n)]) for i in range(n)]

    C1 = dgmul_right(matmul(dgmul_right(H, lam), H), mu)         # H Λ H M
    C1h = dgmul_right(matmul(dgmul_right(H, mu), H), lam)        # H M H Λ

    def solve(C, rhss):
        """Solve (1 + ω C) x = rhs for each rhs, by Gaussian elimination with unit pivots."""
        A = [[(const(1) if i == j else zero()) for j in range(n)] for i in range(n)]
        for i in range(n):
            for j in range(n):
                A[i][j] = sadd(A[i][j], sscale(w, C[i][j]))
        M = [row[:] + [r[i] for r in rhss] for i, row in enumerate(A)]
        for i, row in enumerate(M):     # augment: columns n..n+len(rhss)-1
            M[i] = row
        ncol = n + len(rhss)
        for col in range(n):
            piv = next((i for i in range(col, n) if M[i][col][0] != 0), None)
            if piv is None: raise RuntimeError("no unit pivot in column %d" % col)
            M[col], M[piv] = M[piv], M[col]
            inv = M[col][col]
            M[col] = [sdiv(e, inv) for e in M[col]]
            for i in range(n):
                if i != col and not iszero(M[i][col]):
                    f = M[i][col]
                    M[i] = [ssub(M[i][j], smul(f, M[col][j])) for j in range(ncol)]
        return [[M[i][n + k] for i in range(n)] for k in range(len(rhss))]

    e0 = [const(1) if a == 0 else zero() for a in range(n)]
    e1 = [const(1) if a == 1 else zero() for a in range(n)]
    p, g0, g1 = solve(C1, [v, e0, e1])
    (ph,) = solve(C1h, [v])
    q = matvec(dgmul_right(H, lam), ph)
    qh = matvec(dgmul_right(H, mu), p)
    A = lambda x: [sscale(a, x[a]) for a in range(n)]
    dot = lambda x, y: sadd(*[smul(x[a], y[a]) for a in range(n)])
    Mv = [sscale(mu[a], v[a]) for a in range(n)]
    Lv = [sscale(lam[a], v[a]) for a in range(n)]
    MAv, LAv = A(Mv), A(Lv)
    return dict(P=dot(Mv, p), Q=dot(Mv, q), Ph=dot(Lv, ph), Qh=dot(Lv, qh),
                P1=dot(MAv, p), Q1=dot(MAv, q), Ph1=dot(LAv, ph), Qh1=dot(LAv, qh),
                p0=p[0], q0=q[0], ph0=ph[0], qh0=qh[0],
                G00=g0[0], G01=g1[0], G10=g0[1], G11=g1[1])

# ----------------------------------------------------- leg B: partitions ----
def partitions_of(k, most=None):
    if k == 0:
        yield []
        return
    most = k if most is None else min(most, k)
    for first in range(most, 0, -1):
        for rest in partitions_of(k - first, first):
            yield [first] + rest

def partition_leg(t, w, Nmax):
    """G₀, G₁, Ĝ₁, G₂ as series in r (only even powers), by enumeration."""
    G0, G1, G1h, G2 = zero(), zero(), zero(), zero()
    for size in range(0, Nmax + 1):
        if 2 * size > N: break
        for lam in partitions_of(size):
            conj = [sum(1 for p in lam if p > j) for j in range(lam[0])] if lam else []
            hook = 1
            wt = F(1)
            for i, part in enumerate(lam):
                for j in range(part):
                    hook *= (part - j) + (conj[j] - i) - 1
                    wt *= ((j - i - 1) ** 2 - t)
            wt = F(wt, hook ** 2) if isinstance(wt, int) else wt / F(hook ** 2)
            d = sum(1 for i, part in enumerate(lam) if part >= i + 1)
            n1 = sum(1 for i, part in enumerate(lam) if part - (i + 1) >= 1)
            n2 = sum(1 for i, part in enumerate(lam) if part - (i + 1) >= 2)
            n1h = sum(1 for j, col in enumerate(conj) if col - (j + 1) >= 1)
            k = 2 * size
            G0[k] += w ** d * wt
            G1[k] += w ** n1 * wt
            G1h[k] += w ** n1h * wt
            G2[k] += w ** n2 * wt
    return G0, G1, G1h, G2

def partition_leg_omega(t, Nmax):
    """G₀, G₂ with ω kept symbolic: coefficient of q^n is a list indexed by the power of ω.
    Checking the identity termwise in ω is Conjecture 3.2 for each k separately."""
    G0 = [[F(0)] * (Nmax + 2) for _ in range(Nmax + 1)]
    G2 = [[F(0)] * (Nmax + 2) for _ in range(Nmax + 1)]
    for size in range(0, Nmax + 1):
        for lam in partitions_of(size):
            conj = [sum(1 for p in lam if p > j) for j in range(lam[0])] if lam else []
            hook, wt = 1, F(1)
            for i, part in enumerate(lam):
                for j in range(part):
                    hook *= (part - j) + (conj[j] - i) - 1
                    wt *= ((j - i - 1) ** 2 - t)
            wt = wt / F(hook ** 2)
            d = sum(1 for i, part in enumerate(lam) if part >= i + 1)
            n2 = sum(1 for i, part in enumerate(lam) if part - (i + 1) >= 2)
            G0[size][d] += wt
            G2[size][n2] += wt
    return G0, G2

def check_conjecture(t, Nmax):
    """d/dq G₀ = ω((1−t) G₂ + q d/dq G₂), termwise in q and ω.
    The coefficient of q^N ω^k is  (N+1)·[q^{N+1}ω^k] G₀ = (1−t+N)·[q^N ω^{k−1}] G₂,
    which is Conjecture 3.2 for that k and N."""
    G0, G2 = partition_leg_omega(t, Nmax)
    bad = []
    for n in range(Nmax):
        for k in range(Nmax + 1):
            lhs = (n + 1) * G0[n + 1][k]
            rhs = ((1 - t) + n) * (G2[n][k - 1] if k >= 1 else F(0))
            if lhs != rhs: bad.append((n, k))
    return bad

# --------------------------------------------------------------- R6, R7 ----
def load_R7():
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'zR7_terms.txt')
    terms = []
    for line in open(path):
        if line.startswith('#') or not line.strip(): continue
        f = line.split()
        terms.append((F(f[0]), tuple(int(x) for x in f[1:])))
    return terms

def eval_R7(terms, t, w, S):
    """Σ coeff · r^i t^j ω^k P^l Q^m P₁^n, evaluated on series."""
    acc = zero()
    cache = {}
    def pw(name, e):
        if (name, e) not in cache: cache[(name, e)] = spow(S[name], e)
        return cache[(name, e)]
    for c, (i, j, k, l, m, nn) in terms:
        coef = c * (F(t) ** j) * (F(w) ** k)
        term = sscale(coef, mono(i))
        if l: term = smul(term, pw('P', l))
        if m: term = smul(term, pw('Q', m))
        if nn: term = smul(term, pw('P1', nn))
        acc = sadd(acc, term)
    return acc

def eval_R6(t, w, S):
    """u·R6 = (P2 quadratic) − u(t P₁ + (t(1−t)/2)(P − (1−t)u²P̂)), u = 1 − r²."""
    P, Ph, Q, P1, Q1 = S['P'], S['Ph'], S['Q'], S['P1'], S['Q1']
    r = mono(1); u = ssub(const(1), mono(2))
    wr = sscale(w, r)
    P2num = sadd(smul(smul(wr, u), ssub(sadd(smul(P, Q1), smul(P1, Q)),
                                        smul(wr, smul(P, smul(Q, Q))))),
                 smul(smul(wr, sadd(const(1), mono(2))), smul(P, Q)),
                 sneg(sscale(t, smul(mono(2), P))),
                 sneg(sscale(w, smul(mono(2), smul(u, smul(smul(P, P), Ph))))))
    rhs = smul(u, sadd(sscale(t, P1),
                       sscale(F(t) * (1 - F(t)) / 2,
                              ssub(P, sscale(1 - F(t), smul(spow(u, 2), Ph))))))
    return ssub(P2num, rhs)

# ----------------------------------------------------------------- main -----
def run(t, w, n, Nmax, verbose=True):
    t, w = F(t), F(w)
    S = matrix_leg(t, w, n)
    G0, G1, G1h, G2 = partition_leg(t, w, Nmax)
    r = mono(1); u = ssub(const(1), mono(2)); one = const(1)
    res = {}
    lim = 2 * Nmax - 4          # partition data is reliable to r^(2 Nmax); leave margin for the
                                # shifted division used to recover P̂

    # --- the two legs against each other -----------------------------------
    res['Q from (log G0)\' = 2ω Q'] = ssub(sderiv(G0), sscale(2 * w, smul(G0, S['Q'])))
    res['P = (1−t)(1−r²) G₁/G₀'] = ssub(smul(S['P'], G0), sscale(1 - t, smul(u, G1)))

    # --- Conjecture 3.2, from partitions alone ------------------------------
    # d/dq G₀ = ω((1−t) G₂ + q d/dq G₂),  q = r²,  d/dq = (1/2r) d/dr
    res['(C′_z) from partitions'] = ssub(
        sderiv(G0), sscale(2 * w, smul(r, sadd(sscale(1 - t, G2),
                                               sscale(F(1, 2), smul(r, sderiv(G2)))))))

    # --- first integrals on the matrix leg ---------------------------------
    P, Ph, Q, P1, Q1, Ph1, Qh1 = (S[k] for k in ('P', 'Ph', 'Q', 'P1', 'Q1', 'Ph1', 'Qh1'))
    res['R1'] = sadd(smul(u, ssub(Q1, Qh1)), sscale(2, smul(mono(2), Q)))
    res['R2'] = ssub(sadd(Q1, Qh1, Q), sadd(smul(r, smul(P, Ph)),
                                            sscale(w, smul(r, smul(Q, Q)))))
    res['R3'] = ssub(smul(spow(u, 2), ssub(smul(P, Ph1), smul(Ph, P1))),
                     sadd(sscale(2, smul(mono(2), smul(u, smul(P, Ph)))), sscale(2, smul(r, Q))))
    res['R6 (matrix leg)'] = eval_R6(t, w, S)
    R7terms = load_R7()
    res['R7 (matrix leg)'] = eval_R7(R7terms, t, w, S)

    # --- first integrals on partition-derived scalars ----------------------
    # P, Q, P̂ from the generating functions; P₁ from the proved ODE r P' = 2P₁ − 2ωrPQ
    Pp = sscale(1 - t, smul(u, sdiv(G1, G0)))
    Qp = sscale(F(1, 2) / w, sdiv(sderiv(G0), G0))
    # P̂ and P₁ from equations already proved (and machine-checked in batch 5):
    #   r Q′ = 2 r P P̂ − Q   and   r P′ = 2 P₁ − 2 ω r P Q,
    # so the partition leg uses no matrix input at all.
    Php = sdiv_shift(sadd(smul(r, sderiv(Qp)), Qp), sscale(2, smul(r, Pp)))
    P1p = sscale(F(1, 2), sadd(smul(r, sderiv(Pp)), sscale(2 * w, smul(r, smul(Pp, Qp)))))
    Q1p = zero()                                   # r Q₁′ = 2 r P̂ P₁ − Q₁, integrated
    prod = smul(Php, P1p)
    for k in range(1, N + 1):
        Q1p[k] = 2 * prod[k - 1] / (k + 1)
    res['P̂ from the Q-equation'] = ssub(Php, S['Ph'])
    res['Q₁ from its equation'] = ssub(Q1p, S['Q1'])
    Sp = dict(P=Pp, Ph=Php, Q=Qp, P1=P1p, Q1=Q1p)
    res['R6 (partition leg)'] = eval_R6(t, w, Sp)
    res['R7 (partition leg)'] = eval_R7(R7terms, t, w, Sp)

    # --- closed forms (matrix leg) -----------------------------------------
    xi = 1 - w
    p0, q0, ph0, qh0 = S['p0'], S['q0'], S['ph0'], S['qh0']
    res['(I3a) ξ p₀p̂₀'] = ssub(sscale(xi, smul(p0, ph0)),
                               ssub(one, sscale(w / (1 - t), ssub(smul(u, smul(P, Ph)),
                                                                  smul(r, Q)))))
    res['(I3b) ξ p₀²'] = ssub(sscale(xi, smul(p0, p0)),
                              ssub(ssub(one, sscale(w, smul(spow(u, 2), smul(P, Ph)))),
                                   sscale(w / (t * (1 - t) ** 2),
                                          spow(ssub(P1, sscale(t, P)), 2))))
    res['(I4) ξ(1−r²) 𝒢₀₀'] = ssub(sscale(xi, smul(u, S['G00'])),
                                    ssub(u, sscale(w / (1 - t), P)))
    res['(G01)'] = ssub(sscale(xi * (1 - t), smul(r, smul(u, S['G01']))),
                        sscale(w, sadd(smul(u, P1), sscale(t, smul(mono(2), P)))))
    res['(G10) 𝒢₀₁ + t 𝒢₁₀'] = sadd(S['G01'], sscale(t, S['G10']))
    res['(G11)'] = ssub(sscale(xi, smul(mono(2), smul(u, S['G11']))),
                        sadd(smul(mono(2), u),
                             sscale(w / (1 - t), smul(P, sadd(mono(2), sscale(1 - t,
                                    ssub(one, sscale(2, mono(2))))))),
                             sscale(2 * w / (1 - t), smul(u, P1)),
                             sneg(sscale(w * (1 - t), smul(spow(u, 4), Ph)))))
    # --- the target on the matrix leg --------------------------------------
    rho = sscale(F(1, 1) / (w * w),
                 ssub(smul(ssub(one, sscale(xi, S['G00'])), ssub(one, sscale(xi, S['G11']))),
                      sscale(xi * xi, smul(S['G01'], S['G10']))))
    res['(C′_z) from the resolvent'] = ssub(
        sadd(smul(mono(2), sderiv(rho)), sscale(2 * (1 - t), smul(r, rho))),
        sscale(2, smul(Q, ssub(one, sscale(w, smul(mono(2), rho))))))

    ok = True
    for k, s in res.items():
        good = iszero(s, lim)
        ok = ok and good
        if verbose:
            print("    %-34s %s" % (k, "OK" if good else "FAIL (first defect r^%s)" % firstnz(s)))
    return ok


if __name__ == "__main__":
    order = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    N = order
    points = [(F(-23, 10), F(3, 5)), (F(-7, 3), F(2, 7)), (F(5, 2), F(-3, 4)), (F(1, 3), F(4, 3)),
              (F(4), F(1, 2)), (F(-1), F(-2)), (F(7, 11), F(9, 4)), (F(-100), F(1, 3))]
    print("Conjecture 3.2 termwise in k, by partition enumeration (ω symbolic):")
    for tv in [F(-23, 10), F(-7, 3), F(5, 2), F(1, 3), F(4), F(-1), F(7, 11), F(-100),
               F(9), F(16), F(1, 1000), F(-3)]:
        Nm = 26
        bad = check_conjecture(tv, Nm)
        print("   t = %-9s all k, N ≤ %d :  %s" % (tv, Nm - 1, "OK" if not bad else "FAIL %s" % bad[:4]))
    print()
    allok = True
    for t, w in points:
        print("t = %-8s ω = %-6s (order %d)" % (t, w, N))
        allok &= run(t, w, n=N // 2 + 2, Nmax=N // 2)
    print("ALL OK" if allok else "SOME CHECKS FAILED")
