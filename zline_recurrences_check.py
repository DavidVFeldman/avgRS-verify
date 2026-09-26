"""Exact coefficientwise check of the identities commissioned in COMMISSION.md (batch 5).

Standalone: Python 3 only, no third-party packages, exact rational arithmetic.
Run:  python3 zline_recurrences_check.py            (default t = -23/10, omega = 3/5, order 26)
      python3 zline_recurrences_check.py -7/3 2/7 30

Objects (all series in r = X, truncated at r^N; all vectors indexed by a = 0..n-1):

    H_ab = r^(a+b+1)/(a! b! (a+b+1)),   v_a = r^a/a!
    lam_b = prod_{m<b} ((m+2)^2 - t),   mu_a = (1-t) prod_{m<a} (m^2 - t)
    Lam = diag(lam),  M = diag(mu),  C1 = H Lam H M,  C1h = H M H Lam
    G  = (1 + omega C1)^{-1},   Gh = (1 + omega C1h)^{-1}
    p  = G v,   ph = Gh v,   q = H Lam ph,   qh = H M p,   c = H Lam v
    P  = <Mv, p>,  Q = <Mv, q>,  Phat = <Lam v, ph>,  Qhat = <Lam v, qh>
    P1 = <M Av, p>,  Q1 = <M Av, q>,  Phat1 = <Lam v, A ph>,  Qhat1 = <Lam v, A qh>
    A  = diag(a),  (X f)_a = a f_{a-1},  (X^T f)_a = (a+1) f_{a+1},  D_k = (A+k)^2 - t
    u  = 1 - r^2,  sigma = u (P1 - omega r P Q)

Every printed line is an identity of COMMISSION.md; OK means all coefficients of r^0..r^(N-6)
vanish for all indices a < n-4.
"""
from fractions import Fraction as F
from math import factorial
import sys

# ---------------------------------------------------------------- series ----
N = 26                       # truncation order in r
def ser(*pairs):
    s = [F(0)] * (N + 1)
    for k, c in pairs:
        if k <= N:
            s[k] += F(c)
    return s
ZERO = [F(0)] * (N + 1)
ONE = ser((0, 1))
R = ser((1, 1))

def add(*xs):
    out = [F(0)] * (N + 1)
    for x in xs:
        for i in range(N + 1):
            out[i] += x[i]
    return out

def sub(x, y): return [a - b for a, b in zip(x, y)]

def mul(x, y):
    out = [F(0)] * (N + 1)
    for i, xi in enumerate(x):
        if xi:
            for j in range(N + 1 - i):
                if y[j]:
                    out[i + j] += xi * y[j]
    return out

def smul(c, x): return [F(c) * a for a in x]
def deriv(x): return [x[i + 1] * (i + 1) for i in range(N)] + [F(0)]
def iszero(x, upto): return all(x[i] == 0 for i in range(min(upto, N) + 1))

# ------------------------------------------------------------ vector ops ----
def vadd(*vs): return [add(*[v[a] for v in vs]) for a in range(len(vs[0]))]
def vsub(x, y): return [sub(x[a], y[a]) for a in range(len(x))]
def vscale(s, x): return [mul(s, x[a]) for a in range(len(x))]
def vsmul(c, x): return [smul(c, x[a]) for a in range(len(x))]
def dot(x, y):
    out = ZERO
    for a in range(len(x)):
        out = add(out, mul(x[a], y[a]))
    return out

def main(t, w, order):
    global N, ZERO, ONE, R
    N = order
    ZERO, ONE, R = [F(0)] * (N + 1), ser((0, 1)), ser((1, 1))
    n = N // 2 + 2

    # weights and basic objects -------------------------------------------
    lam = [F(1)] * (n + 2)
    for b in range(1, n + 2):
        lam[b] = lam[b - 1] * ((b + 1) ** 2 - t)
    mu = [F(1)] * (n + 2)
    mu[0] = 1 - t
    for a in range(1, n + 2):
        mu[a] = mu[a - 1] * ((a - 1) ** 2 - t)
    lamm = [F(1) / (1 - t)] + lam[:-1]          # (Lam^-)_b = lam_{b-1}, lam_{-1} = 1/(1-t)

    H = [[ser((a + b + 1, F(1, factorial(a) * factorial(b) * (a + b + 1)))) for b in range(n)]
         for a in range(n)]
    v = [ser((a, F(1, factorial(a)))) for a in range(n)]

    def diagv(d, f): return [smul(d[a], f[a]) for a in range(n)]
    def Hv(f):
        return [add(*[mul(H[a][b], f[b]) for b in range(n)]) for a in range(n)]
    def A(f): return [smul(a, f[a]) for a in range(n)]
    def X(f): return [ZERO] + [smul(a, f[a - 1]) for a in range(1, n)]
    def XT(f): return [smul(a + 1, f[a + 1]) for a in range(n - 1)] + [ZERO]
    def Dk(k, f): return [smul((a + k) ** 2 - t, f[a]) for a in range(n)]
    def C1(f): return Hv(diagv(lam, Hv(diagv(mu, f))))
    def C1h(f): return Hv(diagv(mu, Hv(diagv(lam, f))))
    def resolvent(Cop, f):
        g = f[:]
        T = f[:]
        for _ in range(N // 2 + 1):
            T = [smul(-w, y) for y in Cop(T)]
            g = vadd(g, T)
        return g

    p = resolvent(C1, v)
    ph = resolvent(C1h, v)
    q = Hv(diagv(lam, ph))
    qh = Hv(diagv(mu, p))
    c = Hv(diagv(lam, v))
    ch = Hv(diagv(mu, v))
    Mv, Lv = diagv(mu, v), diagv(lam, v)
    MAv, LAv = diagv(mu, A(v)), diagv(lam, A(v))
    P, Q = dot(Mv, p), dot(Mv, q)
    Ph, Qh = dot(Lv, ph), dot(Lv, qh)
    P1, Q1 = dot(MAv, p), dot(MAv, q)
    Ph1, Qh1 = dot(LAv, ph), dot(LAv, qh)
    u = sub(ONE, mul(R, R))
    sig = mul(u, sub(P1, smul(w, mul(R, mul(P, Q)))))

    ok = True
    def check(name, residual_vectors):
        """residual_vectors: a vector (list of series) or a single series."""
        nonlocal ok
        if not isinstance(residual_vectors[0], list):
            residual_vectors = [residual_vectors]
        bad = [a for a, s in enumerate(residual_vectors)
               if a < max(1, len(residual_vectors) - 4) and not iszero(s, N - 6)]
        print("  %-46s %s" % (name, "OK" if not bad else "FAIL at indices %s" % bad[:5]))
        ok = ok and not bad

    print("t = %s, omega = %s, order = %d, indices < %d" % (t, w, N, n))

    # --- A. operator layer -----------------------------------------------
    print(" A. operator layer")
    check("(W1) mu_{a+1} = (a^2-t) mu_a, lam_{a+1} = ((a+2)^2-t) lam_a",
          [ser((0, mu[a + 1] - (a ** 2 - t) * mu[a])) for a in range(n - 1)] +
          [ser((0, lam[a + 1] - ((a + 2) ** 2 - t) * lam[a])) for a in range(n - 1)])
    check("(W2) X^T M = M D_0 X^T  (on p)",
          vsub(XT(diagv(mu, p)), diagv(mu, Dk(0, XT(p)))))
    mum = [F(1)] + mu[:-1]                       # (M^-)_a = mu_{a-1}, mu_{-1} = 1
    nu = [F(1)] * (n + 2)
    for b in range(1, n + 2):
        nu[b] = nu[b - 1] * (b ** 2 - t)
    check("(W3) X M = M^- X   (on p)",
          vsub(X(diagv(mu, p)), diagv(mum, X(p))))
    check("(W4) (1-t) X Lam = N X   (on p)",
          vsub(vsmul(1 - t, X(diagv(lam, p))), diagv(nu, X(p))))
    check("(W6) D_1 N = (1-t) Lam,  D_{-1} M^- = M   (on p)",
          vsub(Dk(1, diagv(nu, p)), vsmul(1 - t, diagv(lam, p))) +
          vsub(Dk(-1, diagv(mum, p)), diagv(mu, p)))
    check("(W5) X^T Lam = Lam D_2 X^T (on p)",
          vsub(XT(diagv(lam, p)), diagv(lam, Dk(2, XT(p)))))
    # (H2) dressed: A H Lam = r v (x) Lam v - H Lam A - H Lam, applied to p
    check("(A1) A W p = r <Lam v,p> v - W A p - W p,  W = H Lam",
          vsub(A(Hv(diagv(lam, p))),
               vsub(vscale(mul(R, dot(Lv, p)), v),
                    vadd(Hv(diagv(lam, A(p))), Hv(diagv(lam, p))))))
    # D_0 H = H D_1 - r [ v (x) (A+1)v - Av (x) v ]   (applied to p)
    check("(A2) D_0 H p (and D_2 H = H D_{-1} + r((A+3)v (x) v - v (x) Av)) = H D_1 p - r(<(A+1)v,p> v - <v,p> Av)",
          vsub(Dk(0, Hv(p)),
               vsub(Hv(Dk(1, p)),
                    vsub(vscale(mul(R, add(dot(A(v), p), dot(v, p))), v),
                         vscale(mul(R, dot(v, p)), A(v))))))
    # (A3)  D_0 H N H = (1-t) H Lam H - r [ v (x) H N (A+1)v - Av (x) H N v ]   (applied to p)
    HN = lambda f: Hv(diagv(nu, f))
    HMm = lambda f: Hv(diagv(mum, f))
    check("(A3) D_0 H N H p = (1-t) H Lam H p - r(<HN(A+1)v,p> v - <HNv,p> Av)",
          vsub(Dk(0, HN(Hv(p))),
               vsub(vsmul(1 - t, Hv(diagv(lam, Hv(p)))),
                    vsub(vscale(mul(R, dot(HN(vadd(A(v), v)), p)), v),
                         vscale(mul(R, dot(HN(v), p)), A(v))))))
    # (A3h) D_2 H M^- H = H M H + r [ (A+3)v (x) H M^- v - v (x) H M^- Av ]      (applied to ph)
    check("(A3h) D_2 H M^- H ph = H M H ph + r(<HM^-v,ph> (A+3)v - <HM^-Av,ph> v)",
          vsub(Dk(2, HMm(Hv(ph))),
               vadd(Hv(diagv(mu, Hv(ph))),
                    vscale(mul(R, dot(HMm(v), ph)), vadd(A(v), vsmul(3, v))),
                    vscale(smul(-1, mul(R, dot(HMm(A(v)), ph))), v))))
    # [A, C1] = r (v (x) Mc - c (x) Mv)   (applied to p)
    check("(A4) [A,C1] p = r(<Mc,p> v - <Mv,p> c)",
          vsub(vsub(A(C1(p)), C1(A(p))),
               vsub(vscale(mul(R, dot(diagv(mu, c), p)), v), vscale(mul(R, P), c))))
    # [X, C1] p, five terms
    L0 = dot(Lv, v)
    check("(A5) [X,C1] p (five-term formula)",
          vsub(vsub(X(C1(p)), C1(X(p))),
               vadd(vscale(dot(diagv(mu, c), p), A(v)),
                    vscale(dot(vadd(A(diagv(mu, c)), diagv(mu, c)), p), v),
                    vscale(smul(-1, mul(mul(R, R), P)), vsub(A(c), c)),
                    vscale(smul(-1, mul(mul(R, R), dot(A(Mv), p))), c),
                    vscale(smul(-1, mul(mul(R, mul(u, L0)), P)), v))))

    # --- B. resolvent layer ----------------------------------------------
    print(" B. resolvent layer")
    check("(B1) G H Lam = H Lam Gh  (on v)", vsub(q, Hv(diagv(lam, ph))))
    check("(B2) omega H M q = v - ph", vsub(vsmul(w, Hv(diagv(mu, q))), vsub(v, ph)))
    check("(B3) Q = Qhat", sub(Q, Qh))
    check("(B4) G A v = A p + omega r (Q p - P q)",
          vsub(vsub(resolvent(C1, A(v)), A(p)),
               vscale(smul(w, R), vsub(vscale(Q, p), vscale(P, q)))))
    check("(B5) p' = A p / r - 2 omega P q",
          vsub(vscale(R, [deriv(x) for x in p]),
               vsub(A(p), vscale(smul(2 * w, mul(R, P)), q))))
    check("(B6) q' = 2 Phat p - (A+1) q / r",
          vsub(vscale(R, [deriv(x) for x in q]),
               vsub(vscale(smul(2, mul(R, Ph)), p), vadd(A(q), q))))
    check("(B7) ph' = A ph / r - 2 omega Phat qh",
          vsub(vscale(R, [deriv(x) for x in ph]),
               vsub(A(ph), vscale(smul(2 * w, mul(R, Ph)), qh))))
    check("(B8) qh' = 2 P ph - (A+1) qh / r",
          vsub(vscale(R, [deriv(x) for x in qh]),
               vsub(vscale(smul(2, mul(R, P)), ph), vadd(A(qh), qh))))
    check("(B9) R2: Q1 + Qhat1 + Q = r P Phat + omega r Q^2",
          sub(add(Q1, Qh1, Q), add(mul(R, mul(P, Ph)), smul(w, mul(R, mul(Q, Q))))))

    # --- C. the three recurrences ----------------------------------------
    print(" C. recurrences")
    check("(RXp) r X p = A^2 p - omega r u P Aq - omega r (sig + r^2 P) q "
          "+ omega r (r u P Phat - Q) p",
          vsub(vscale(R, X(p)),
               vadd(A(A(p)),
                    vscale(smul(-w, mul(R, mul(u, P))), A(q)),
                    vscale(smul(-w, mul(R, add(sig, mul(mul(R, R), P)))), q),
                    vscale(smul(w, mul(R, sub(mul(R, mul(u, mul(P, Ph))), Q))), p))))
    check("(RZp) D_0 X^T p = r A^2 p + omega u P Aq + omega (sig + P) q "
          "+ (omega r^2 Q - r t - omega r u P Phat) p",
          vsub(Dk(0, XT(p)),
               vadd(vscale(R, A(A(p))),
                    vscale(smul(w, mul(u, P)), A(q)),
                    vscale(smul(w, add(sig, P)), q),
                    vscale(add(smul(w, mul(mul(R, R), Q)), smul(-t, R),
                               smul(-w, mul(R, mul(u, mul(P, Ph))))), p))))
    check("(RZph) D_2 X^T ph = r A^2 ph + 4 r A ph + omega u Phat Aqh "
          "+ omega((1-4r^2)Phat + u Phat1 - omega r u Phat Q) qh "
          "+ ((4-t) r + omega r^2 Q - omega r u P Phat) ph",
          vsub(Dk(2, XT(ph)),
               vadd(vscale(R, A(A(ph))),
                    vscale(smul(4, R), A(ph)),
                    vscale(smul(w, mul(u, Ph)), A(qh)),
                    vscale(smul(w, add(mul(sub(ONE, smul(4, mul(R, R))), Ph),
                                       mul(u, Ph1),
                                       smul(-w, mul(R, mul(u, mul(Ph, Q)))))), qh),
                    vscale(add(smul(4 - t, R), smul(w, mul(mul(R, R), Q)),
                               smul(-w, mul(R, mul(u, mul(P, Ph))))), ph))))
    P2 = dot(diagv(mu, A(A(v))), p)
    check("(C4) u P2 = omega r u (P Q1 + P1 Q - omega r P Q^2) "
          "+ omega r (1+r^2) P Q - r^2 t P - omega r^2 u P^2 Phat",
          sub(mul(u, P2),
              add(smul(w, mul(R, mul(u, sub(add(mul(P, Q1), mul(P1, Q)),
                                            smul(w, mul(R, mul(P, mul(Q, Q)))))))),
                  smul(w, mul(R, mul(add(ONE, mul(R, R)), mul(P, Q)))),
                  smul(-t, mul(mul(R, R), P)),
                  smul(-w, mul(mul(R, R), mul(u, mul(mul(P, P), Ph)))))))
    print("ALL OK" if ok else "SOME CHECKS FAILED")
    return ok


if __name__ == "__main__":
    t = F(sys.argv[1]) if len(sys.argv) > 1 else F(-23, 10)
    w = F(sys.argv[2]) if len(sys.argv) > 2 else F(3, 5)
    order = int(sys.argv[3]) if len(sys.argv) > 3 else 26
    main(t, w, order)
