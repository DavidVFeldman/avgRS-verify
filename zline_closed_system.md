# The two-matrix resolvent on the line z + z' = −2: closed system found

Independent recomputation (2026-09-25, `zline_scripts/zindependent.py`): R6, R7, the closed forms
(I3a), (I3b), (I4), (G01), (G11), R1, R2, R3 and the target (C'_z) were recomputed in pure Python
with exact rationals, with the resolvent obtained by Gaussian elimination rather than a Neumann
series, and cross-checked against a second leg that enumerates partitions and uses no matrices at
all (P from (1-t)(1-r^2)G_1/G_0, Q from (log G_0)' = 2wQ, then P-hat, P_1, Q_1 from the proved
scalar equations). All 19 checks pass at 8 parameter pairs to order 34. R6 and R7 pass on both
legs. Separately, Conjecture 3.2 itself was verified termwise in k -- not merely in an
omega-weighted sum -- at 12 rational values of t for all k and all N <= 25.

Status (2026-09-26): Conjecture 3.2 has a complete proof skeleton in Lean (batch 6) that does not
compile: three lemmas are single linear_combination calls of 70k-155k characters, two of which
exhaust memory. Not proved until it builds. Previously: the operator layer, the resolvent layer, the recurrences and the first
integral R2 are formalized in Lean (Aristotle batch 5, `RequestProject/ZLineRec.lean`), pending a
cold build with an axiom audit. Every identity below is verified exactly on formal power series in r
(orders 34–200, four parameter pairs (t,ω), including ω<0 and t>0), and the algebraic
consequences are verified as exact polynomial identities over ℚ(t,ω) (ideal membership, flint).
Items marked [derived] have hand derivations that reproduce the verified coefficients; items
marked [first integral] are proved by D-closure + zero initial data (valuation argument to be
written); the conjecture follows from the whole list by the exact computation `zproof.py`.

## Setup (r = √q; conjugation by diag(z(z+1)_a) removes z from H_z)
H_ab = r^{a+b+1}/(a!b!(a+b+1)), v_a = r^a/a!  (Plancherel objects)
Λ = diag(λ_b), λ_b = ∏_{m<b}((m+2)²−t);   M = diag(μ_a), μ_a = (1−t)∏_{m<a}(m²−t)
C₁ = HΛHM, 𝒢₁ = (1+ωC₁)⁻¹ ;   Ĉ₁ = HMHΛ, 𝒢̂₁ = (1+ωĈ₁)⁻¹ ;   HΛ𝒢̂₁ = 𝒢₁HΛ, HM𝒢₁ = 𝒢̂₁HM
G₀ = det(1+ωC₁) = Σ_λ ω^{d(λ)} w_t(λ) q^{|λ|},  G₂ = det(1+ΩC₁), Ω = diag(1,1,ω,ω,…)
Conjecture 3.2 ⟺ (1/2r) G₀' = ω((1−t)G₂ + (r/2)G₂')  ⟺ with ρ = G₂/G₀:
   (C'_z)   r²ρ' + 2r(1−t)ρ = 2Q(1 − r²ωρ),   ρ = [(1−ξ𝒢₀₀)(1−ξ𝒢₁₁) − ξ²𝒢₀₁𝒢₁₀]/ω²,  ξ = 1−ω
Vectors: p = 𝒢₁v, q = 𝒢₁HΛv = HΛp̂, p̂ = 𝒢̂₁v, q̂ = 𝒢̂₁HMv = HMp.
Scalars: P = ⟨Mv,p⟩, Q = ⟨Mv,q⟩ = ⟨Λv,q̂⟩, P̂ = ⟨Λv,p̂⟩, P₁ = ⟨MAv,p⟩, P̂₁ = ⟨ΛAv,p̂⟩,
         Q₁ = ⟨MAv,q⟩, Q̂₁ = ⟨ΛAv,q̂⟩, P₂ = ⟨MA²v,p⟩, P̂₂ = ⟨ΛA²v,p̂⟩.  u := 1−r².
(log G₀)' = 2ωQ.  P = (1−t)(1−r²) G₁/G₀ with G₁ = Σ ω^{N₁} w_t q^{|λ|}  (from (I4_z) below).

## S0 and R8 (Aristotle batch 6; S0 and R8 verified here independently)
S0 [proved]: differentiate the level-0 relation (sigma + r^2 P) q0 = (r u P Phat - Q) p0, substitute
the ODEs, cancel the units X, P, p0, 1-X^2. This yields a first integral in P, Phat, Q, P1, Phat1
(28 terms) from which R3, R1, R6 and R7 follow in that order -- so R6 and R7 are now theorems, not
conjectures. Eliminating Phat1 between S0 and R3 gives (r^2-1) times a 33-term relation R8, and R7
is the further eliminant of R8 and R6 (which is why R7 has 169 terms and no good form). R8 in
grouped form, exactly:

  u sigma^2 Phat = -u^3 r^2 w Phat^2 P^3 + u^2 r Phat P^2 (w(r^2+1)Q - t r)
                   + u (r^2 Phat P^2 + r^2 w P Q^2 + t r P Q - 2 r P1 Q) - r(r^2+1) P Q,

the analogue of the Plancherel first integral sigma^2 = beta W. Carry {S0, R1, R3, R6, R8}; R7
should never be formed.

## Adjointness (the reason the twisted shifts work) [proved; verified]
With the pairing ⟨f,g⟩_M = ⟨Mf,g⟩: XᵀM = MD₀Xᵀ says D₀Xᵀ is the M-adjoint of X, and C₁ is
M-self-adjoint; likewise D₂Xᵀ is the Λ-adjoint of X and Ĉ₁ is Λ-self-adjoint. Hence
  [D₀Xᵀ, C₁] = −[X,C₁]*   (M-adjoint),   [D₂Xᵀ, Ĉ₁] = −[X,Ĉ₁]*   (Λ-adjoint),
so the two twisted commutators are the plain one read backwards, and the recurrences (RZp), (RZp̂)
follow from (RXp)'s ingredients alone. The auxiliary weights N = diag(∏_{j≤b}(j²−t)) and
M⁻ = diag(μ_{a−1}) and the identities D₀HNH = (1−t)HΛH − rank two, D₂HM⁻H = HMH + rank two are
then unnecessary scaffolding (they are proved in Lean but not needed). Closed forms, up to X^m for
the truncations and exactly in the limit (Aristotle, batch 5; verified here at all indices):
  [D₀Xᵀ,C₁] = r(1−r²)⟨Λv,v⟩ v⊗Mv + r² v⊗M(A−1)c + r² Av⊗Mc − c⊗MAv − (A+1)c⊗Mv,  c = HΛv
  [D₂Xᵀ,Ĉ₁] = r(1−r²)⟨Mv,v⟩ v⊗Λv + r² v⊗Λ(A+3)ĉ + r² Av⊗Λĉ − ĉ⊗ΛAv − (A+1)ĉ⊗Λv,  ĉ = HMv

## Operator identities [proved]
XᵀH = HX; XH − HXᵀ = [A,v⊗v]; HA + (A+1)H = r v⊗v; Xᵀv = rv; A²v = rXv;
XᵀM = MD₀Xᵀ, XM = MD₋₁⁻¹X, XᵀΛ = ΛD₂Xᵀ, XΛ = ΛD₁⁻¹X,  D_k := (A+k)² − t;
HD₀ = D₁H + r v⊗Av − r(A+1)v⊗v;  HD₁ = D₀H + r v⊗(A+1)v − rAv⊗v;
HD₂ = D₋₁H + r v⊗(A+2)v + r(1−A)v⊗v;  HD₋₁ = D₂H + r v⊗(A−1)v − r(A+2)v⊗v.
[A,C₁] = r(v⊗Mc − c⊗Mv), c = HΛv;  [X,C₁] = Av⊗Mc + v⊗M(A+1)c − r²(A−1)c⊗Mv − r²c⊗AMv − r(1−r²)⟨v,Λv⟩ v⊗Mv.
Key structural fact: D₀Xᵀ C₁ = C₁ D₀Xᵀ + finite rank, D₂Xᵀ Ĉ₁ = Ĉ₁ D₂Xᵀ + finite rank
(and [X,C₁], [Xᵀ,C₁] finite rank because [A,C₁] is).

## Resolvent identities and ODEs [proved as in Section 5]
𝒢₁' = −ω(p⊗Mq + q⊗Mp);  [A,𝒢₁] = −ωr(p⊗Mq − q⊗Mp);  hat versions with Λ.
p' = Ap/r − 2ωPq,  q' = 2P̂p − (A+1)q/r,  p̂' = Ap̂/r − 2ωP̂q̂,  q̂' = 2Pp̂ − (A+1)q̂/r.
Hence for any r-independent weight W: ⟨WA^kv,p⟩' = 2⟨WA^{k+1}v,p⟩/r − 2ωP⟨WA^kv,q⟩, etc.:
P' = 2P₁/r − 2ωPQ, P̂' = 2P̂₁/r − 2ωP̂Q, Q' = 2PP̂ − Q/r, Q₁' = 2P̂P₁ − Q₁/r, Q̂₁' = 2PP̂₁ − Q̂₁/r,
P₁' = 2P₂/r − 2ωPQ₁, P̂₁' = 2P̂₂/r − 2ωP̂Q̂₁.

## Recurrences [derived; hypergeometric constants ⟨v,Λv⟩ etc. cancel]  σ := u(P₁ − ωrPQ)
(RXp)  X p   = A²p/r − ωuP·Aq − ω(σ + r²P)·q + ω(ruPP̂ − Q)·p
(RZp)  D₀Xᵀp = rA²p + ωuP·Aq + ω(σ + P)·q + (ωr²Q − rt − ωruPP̂)·p
(RZp̂)  D₂Xᵀp̂ = rA²p̂ + 4r·Ap̂ + ωuP̂·Aq̂ + [ω(1−4r²)P̂ + ωuP̂₁ − ω²ruP̂Q]·q̂ + [(4−t)r + ωr²Q − ωruPP̂]·p̂
Consequences: P₂ = r⟨Mv,D₀Xᵀp⟩ gives
  (P2q)  uP₂ = ωru(PQ₁ + P₁Q − ωrPQ²) + ωr(1+r²)PQ − r²tP − ωr²uP²P̂
         [exact in the limit; for the m×m truncations only up to X^m — the defect starts at r^{2m}]
  (P̂2q)  uP̂₂ = 4r²P̂₁ + ωruP̂(Q₁+Q̂₁+Q) + ωr(1−4r²)P̂Q + ωruP̂₁Q − ω²r²uP̂Q² + (4−t)r²P̂ + ωr³QP̂ − ωr²uPP̂²
          [= ωru(QP̂₁ − P̂Q₁) − 2ωr³P̂Q + (4−t)r²P̂ + 4r²P̂₁ modulo R2]
Index 0 of (RXp): (σ + r²P) q₀ = (ruPP̂ − Q) p₀.   Index 0 of (RZp): −t p₁ = ω(σ+P)q₀ + (ωr²Q − rt − ωruPP̂)p₀.
Index 1 of (RXp): p₀ = p₁/r − ωuPq₁ − ω(σ+r²P)q₁ + ω(ruPP̂ − Q)p₁.

## First integrals [D-closure verified exactly; zero at r=0]
R1: u(Q₁ − Q̂₁) = −2r²Q
R2: Q₁ + Q̂₁ + Q = rPP̂ + ωrQ²                      (R2' ≡ 0 identically from the ODEs)
R3: u²(PP̂₁ − P̂P₁) = 2r²uPP̂ + 2rQ                  (R1' ∝ R3)
R6: P₂ = tP₁ + (t(1−t)/2)(P − (1−t)u²P̂)             (i.e. the quadratic (P2q) equals this linear form)
R7: a polynomial relation in (P,Q,P₁) alone, quadratic in σ: A σ² + B σ + C = 0 with
    A = (t−ωrQ)(ωr²P² − t(1−t)²u²), B = −2ωr²u(t−ωrQ)²P³, C = (t−ωrQ)C₁ − (t/ω)(ωr²P² − t(1−t)²u²)²
    (R7 = residue of R6' modulo R6; full form in scratch R7_inner.pkl; no nicer form found yet)
Equivalent: Θ := QP₁ − PQ₁ satisfies u(P₂ − ωrΘ) = −tr²P  (R4).

## Closed forms [each proved by the log-derivative argument, exactly modulo the ideal]
(I3a) ξ p₀p̂₀ = 1 − ω[uPP̂ − rQ]/(1−t)
(I3b) ξ p₀²  = 1 − ωu²PP̂ − ω(P₁ − tP)²/(t(1−t)²)
(I4)  ξ 𝒢₀₀ = 1 − ωP/((1−t)u)                                   ⟹ G₁/G₀ = P/((1−t)u)
(G01) ξ(1−t) r u 𝒢₀₁ = ω[uP₁ + t r²P],   𝒢₁₀ = −𝒢₀₁/t
(G11) ξ(1−t) r²u 𝒢₁₁ = (1−t)r²u + ωP[r² + (1−t)(1−2r²)] + 2ωuP₁ − ω(1−t)²u⁴P̂
(also ξ𝒢̂₀₀, ξrp₀q̂₀, ξrp̂₀q₀, ξru p₀q₀ in polynomial form; see zcheck_all.py)
Final: (C'_z) ∈ ideal(R1,R2,R3,R6,R7) after substituting (I4),(G01),(G11) and the ODEs — exact (zproof.py).

## Scripts (scratchpad)
zform2.py (exact formal engine, fmpq_series), zmodeng.py (mod-p engine), zmod.py/zlev*.py (relation
searches), zdisc.py/zdisc_mod.py (recurrence discovery over ℚ((r))), zcheck_all.py (all identities,
4 parameter points), zideal.py (flint pseudo-reduction, D-closure), zproof.py (closed forms + target,
exact), zfinal.py/zr7*.py (sympy derivation of R7).
