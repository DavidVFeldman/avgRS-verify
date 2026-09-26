module

public import Mathlib
public import RequestProject.RingKernel
public meta import Mathlib
public meta import RequestProject.RingKernel

/-!
# A reflective commutative-ring normaliser for very large identities

`ring_refl` proves a goal `lhs = rhs` in a commutative ring when both sides are equal as
polynomials with integer coefficients in their atoms. It reifies both sides into Lean core's
`Lean.Grind.CommRing.Expr` and closes the goal with `AvgRS.RingKernel.eq_of_toPolyK_eq`, so that
the polynomial normalisation is carried out by the kernel, by evaluation of the kernel-oriented
normaliser `Expr.toPolyK` (see `RequestProject/RingKernel.lean`). No compiled code is trusted:
the proof is checked by the kernel alone. The proof terms are small, and the method scales to
polynomial identities far too large for `ring`.

The recognised operations are `+`, `-` (binary and unary), `*`, `^` with a closed natural-number
exponent, natural-number numerals and casts of closed natural numbers; every other subterm is an
atom (atoms are identified up to reducible definitional equality).
-/

public meta section

namespace AvgRS.RingRefl

open Lean Meta Elab Tactic

/-- State of the reification: the atoms found so far. -/
structure St where
  atoms : Array Expr := #[]
  idx : Std.HashMap Expr Nat := {}

abbrev M := StateT St MetaM

def atomIdx (e : Expr) : M Nat := do
  let s ← get
  match s.idx.get? e with
  | some i => return i
  | none =>
    -- fall back to a defeq check (reducible transparency, as `ring` does) against known atoms
    for h : j in [0:s.atoms.size] do
      if ← withReducible (isDefEq e s.atoms[j]) then
        set { s with idx := s.idx.insert e j }
        return j
    let i := s.atoms.size
    set { s with atoms := s.atoms.push e, idx := s.idx.insert e i }
    return i

private def cE (n : Name) : Expr := mkConst (``Lean.Grind.CommRing.Expr ++ n)

abbrev GE := Lean.Grind.CommRing.Expr

/-- Evaluate a closed natural-number expression (numerals, `+`, `-`, `*`, ...). -/
def evalN (e : Expr) : M (Option Nat) := (evalNat e).run

/-- Reify a term of the ring into a `Lean.Grind.CommRing.Expr`, returned both as a value
(used for a quick check by evaluation) and as a Lean expression (used in the proof term). -/
partial def reify (e : Expr) : M (GE × Expr) := do
  let e := e.consumeMData
  let atom : M (GE × Expr) := do
    let i ← atomIdx e
    return (.var i, mkApp (cE `var) (mkRawNatLit i))
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    let (va, ea) ← reify a; let (vb, eb) ← reify b
    return (.add va vb, mkApp2 (cE `add) ea eb)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    let (va, ea) ← reify a; let (vb, eb) ← reify b
    return (.sub va vb, mkApp2 (cE `sub) ea eb)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    let (va, ea) ← reify a; let (vb, eb) ← reify b
    return (.mul va vb, mkApp2 (cE `mul) ea eb)
  | (``Neg.neg, #[_, _, a]) =>
    let (va, ea) ← reify a
    return (.neg va, mkApp (cE `neg) ea)
  | (``HPow.hPow, #[_, nty, _, _, a, k]) =>
    if nty.isConstOf ``Nat then
      match ← evalN k with
      | some n =>
        let (va, ea) ← reify a
        return (.pow va n, mkApp2 (cE `pow) ea (mkRawNatLit n))
      | none => atom
    else atom
  | (``OfNat.ofNat, #[_, n, _]) =>
    match ← evalN n with
    | some k => return (.num (Int.ofNat k), mkApp (cE `num) (toExpr (Int.ofNat k)))
    | none => atom
  | (``Nat.cast, #[_, _, n]) =>
    match ← evalN n with
    | some k => return (.natCast k, mkApp (cE `natCast) (mkRawNatLit k))
    | none => atom
  | (``NatCast.natCast, #[_, _, n]) =>
    match ← evalN n with
    | some k => return (.natCast k, mkApp (cE `natCast) (mkRawNatLit k))
    | none => atom
  | _ => atom

/-- Close `lhs = rhs` by reflection. -/
def ringRefl (g : MVarId) : MetaM Unit := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (R, lhs, rhs) := t.eq? | throwError "ring_refl: goal is not an equality"
  let u ← getDecLevel R
  let inst ← synthInstance (mkApp (mkConst ``CommRing [u]) R)
  let (((vl, el), (vr, er)), s) ←
    (do return (← reify lhs, ← reify rhs) : M ((GE × Expr) × (GE × Expr))).run {}
  -- a quick check by compiled evaluation, for a readable failure
  unless vl.toPoly == vr.toPoly do
    throwError "ring_refl: the two sides are not equal as polynomials in the atoms {s.atoms}"
  -- the atoms, padded with `0` if there are none
  let zero ← mkNumeral R 0
  let atoms := if s.atoms.isEmpty then #[zero] else s.atoms
  if h : 0 < atoms.size then
    let ctx ← (RArray.ofArray atoms h).toExpr R id
    -- the kernel checks `(toPolyK el).beq' (toPolyK er) = true` by evaluation
    let hT ← mkEqRefl (toExpr true)
    g.assign (mkApp6 (mkConst ``AvgRS.RingKernel.eq_of_toPolyK_eq [u]) R inst ctx el er hT)
  else
    throwError "ring_refl: no atoms"

/-- `ring_refl` closes a commutative-ring identity by kernel evaluation of the polynomial
normal forms (see the module docstring). -/
elab "ring_refl" : tactic => do
  let g ← getMainGoal
  ringRefl g
  replaceMainGoal []

end AvgRS.RingRefl

end
