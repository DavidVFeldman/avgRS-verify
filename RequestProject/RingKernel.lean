module

public import Mathlib

@[expose] public section

/-!
# A kernel-oriented polynomial normaliser

A variant `Expr.toPolyK` of Lean core's `Lean.Grind.CommRing.Expr.toPoly`, written with
recursors so that the kernel can evaluate it efficiently, and in which a product of two
polynomials is computed by iterating over the *shorter* factor. For the very large, very
unbalanced products (a coefficient with thousands of terms times a hypothesis with a few dozen
terms) in the certificates of this project, this makes kernel evaluation feasible.

The main result is `eq_of_toPolyK_eq`: if the normal forms of `a` and `b` agree, then `a` and
`b` denote the same element of any commutative ring.
-/

namespace AvgRS.RingKernel

open Lean.Grind.CommRing

/-- Number of terms of a polynomial. -/
noncomputable def Poly.lenK (p : Poly) : Nat :=
  Poly.rec (fun _ => 1) (fun _ _ _ ih => Nat.succ ih) p

/-- `Poly.mul`, written with recursors (kernel-friendly). -/
noncomputable def Poly.mulK (p₁ p₂ : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun k acc => acc.combine_k (p₂.mulConst_k k))
    (fun k m _ ih acc => ih (acc.combine_k (p₂.mulMon_k k m))) p₁ (.num 0)

theorem Poly.mulK_go (p₁ p₂ acc : Poly) :
    Poly.rec (motive := fun _ => Poly → Poly)
      (fun k acc => acc.combine_k (p₂.mulConst_k k))
      (fun k m _ ih acc => ih (acc.combine_k (p₂.mulMon_k k m))) p₁ acc
      = Poly.mul.go p₂ p₁ acc := by
  induction p₁ generalizing acc with
  | num k => simp [Poly.mul.go]
  | add k m p ih => simp only [Poly.mul.go, ← ih]; simp

theorem Poly.mulK_eq (p₁ p₂ : Poly) : Poly.mulK p₁ p₂ = Poly.mul p₁ p₂ := by
  unfold Poly.mulK Poly.mul; exact Poly.mulK_go p₁ p₂ _

/-- Multiplication iterating over the shorter factor. -/
noncomputable def Poly.mulS (p₁ p₂ : Poly) : Poly :=
  Bool.rec (Poly.mulK p₁ p₂) (Poly.mulK p₂ p₁) (Nat.blt (Poly.lenK p₂) (Poly.lenK p₁))

theorem Poly.denote_mulS {α} [_root_.CommRing α] (ctx : Context α) (p₁ p₂ : Poly) :
    (Poly.mulS p₁ p₂).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  unfold Poly.mulS
  cases Nat.blt (Poly.lenK p₂) (Poly.lenK p₁)
  · simp only [Poly.mulK_eq, Poly.denote_mul]
  · simp only [Poly.mulK_eq, Poly.denote_mul]; exact _root_.mul_comm _ _

/-- `Poly.pow` with the kernel-friendly multiplication. -/
noncomputable def Poly.powK (p : Poly) (k : Nat) : Poly :=
  Nat.rec (.num 1) (fun _ ih => Poly.mulS p ih) k

theorem Poly.denote_powK {α} [_root_.CommRing α] (ctx : Context α) (p : Poly) (k : Nat) :
    (Poly.powK p k).denote ctx = p.denote ctx ^ k := by
  induction k with
  | zero => simp [Poly.powK, Poly.denote]
  | succ k ih =>
    have e : Poly.powK p (k + 1) = Poly.mulS p (Poly.powK p k) := rfl
    rw [e, Poly.denote_mulS, ih, _root_.pow_succ, _root_.mul_comm]

/-- The kernel-oriented normaliser. -/
noncomputable def Expr.toPolyK (e : Expr) : Poly :=
  Expr.rec
    (fun k => .num k) (fun k => .num k) (fun k => .num k)
    (fun x => .ofVar x)
    (fun _ ih => ih.mulConst_k (-1))
    (fun _ _ ih₁ ih₂ => ih₁.combine_k ih₂)
    (fun _ _ ih₁ ih₂ => ih₁.combine_k (ih₂.mulConst_k (-1)))
    (fun _ _ ih₁ ih₂ => Poly.mulS ih₁ ih₂)
    (fun a k ih => Expr.rec (motive := fun _ => Poly)
        (fun n => .num (n ^ k)) (fun n => .num (n ^ k)) (fun n => .num (n ^ k))
        (fun x => Bool.rec (.ofMon (.mult {x, k} .unit)) (.num 1) (k.beq 0))
        (fun _ _ => Poly.powK ih k)
        (fun _ _ _ _ => Poly.powK ih k)
        (fun _ _ _ _ => Poly.powK ih k)
        (fun _ _ _ _ => Poly.powK ih k)
        (fun _ _ _ => Poly.powK ih k)
        a)
    e

theorem Expr.toPolyK_num (k : Int) : Expr.toPolyK (.num k) = .num k := rfl
theorem Expr.toPolyK_natCast (k : Nat) : Expr.toPolyK (.natCast k) = .num k := rfl
theorem Expr.toPolyK_intCast (k : Int) : Expr.toPolyK (.intCast k) = .num k := rfl
theorem Expr.toPolyK_var (x : Var) : Expr.toPolyK (.var x) = .ofVar x := rfl
theorem Expr.toPolyK_neg (a : Expr) :
    Expr.toPolyK (.neg a) = (Expr.toPolyK a).mulConst_k (-1) := rfl
theorem Expr.toPolyK_add (a b : Expr) :
    Expr.toPolyK (.add a b) = (Expr.toPolyK a).combine_k (Expr.toPolyK b) := rfl
theorem Expr.toPolyK_sub (a b : Expr) :
    Expr.toPolyK (.sub a b) = (Expr.toPolyK a).combine_k ((Expr.toPolyK b).mulConst_k (-1)) := rfl
theorem Expr.toPolyK_mul (a b : Expr) :
    Expr.toPolyK (.mul a b) = Poly.mulS (Expr.toPolyK a) (Expr.toPolyK b) := rfl
theorem Expr.toPolyK_pow_num (n : Int) (k : Nat) :
    Expr.toPolyK (.pow (.num n) k) = .num (n ^ k) := rfl
theorem Expr.toPolyK_pow_natCast (n : Nat) (k : Nat) :
    Expr.toPolyK (.pow (.natCast n) k) = .num ((n : Int) ^ k) := rfl
theorem Expr.toPolyK_pow_intCast (n : Int) (k : Nat) :
    Expr.toPolyK (.pow (.intCast n) k) = .num (n ^ k) := rfl
theorem Expr.toPolyK_pow_var (x : Var) (k : Nat) :
    Expr.toPolyK (.pow (.var x) k) = Bool.rec (.ofMon (.mult {x, k} .unit)) (.num 1) (k.beq 0) :=
  rfl

theorem Expr.denote_toPolyK {α} [_root_.CommRing α] (ctx : Context α) (e : Expr) :
    (Expr.toPolyK e).denote ctx = e.denote ctx := by
  induction e with
  | num k => rw [Expr.toPolyK_num]; simp [Poly.denote, Expr.denote, denoteInt_eq]
  | natCast k => rw [Expr.toPolyK_natCast]; simp [Poly.denote, Expr.denote]
  | intCast k => rw [Expr.toPolyK_intCast]; simp [Poly.denote, Expr.denote]
  | var x => rw [Expr.toPolyK_var]; simp [Poly.denote_ofVar, Expr.denote]
  | neg a ih => rw [Expr.toPolyK_neg]; simp [Poly.denote_mulConst, ih, Expr.denote]
  | add a b iha ihb => rw [Expr.toPolyK_add]; simp [Poly.denote_combine, iha, ihb, Expr.denote]
  | sub a b iha ihb =>
    rw [Expr.toPolyK_sub]
    simp [Poly.denote_combine, Poly.denote_mulConst, iha, ihb, Expr.denote, sub_eq_add_neg]
  | mul a b iha ihb => rw [Expr.toPolyK_mul]; simp [Poly.denote_mulS, iha, ihb, Expr.denote]
  | pow a k ih =>
    cases a with
    | num n => rw [Expr.toPolyK_pow_num]; simp [Poly.denote, Expr.denote, denoteInt_eq]
    | natCast n => rw [Expr.toPolyK_pow_natCast]; simp [Poly.denote, Expr.denote]
    | intCast n => rw [Expr.toPolyK_pow_intCast]; simp [Poly.denote, Expr.denote]
    | var x =>
      rw [Expr.toPolyK_pow_var]
      cases hk : k.beq 0
      · have : k ≠ 0 := by rintro rfl; exact absurd hk (by decide)
        simp [Poly.denote_ofMon, Mon.denote, Power.denote_eq, Expr.denote]
      · have : k = 0 := by simpa using hk
        subst this; simp [Poly.denote, Expr.denote]
    | _ =>
      refine (Poly.denote_powK ctx _ k).trans ?_
      exact congrArg (· ^ k) ih

/-- If the kernel-oriented normal forms of `a` and `b` agree, then `a` and `b` are equal in every
commutative ring. -/
theorem eq_of_toPolyK_eq {α : Type u} [_root_.CommRing α] (ctx : Context α)
    (a b : Expr) (h : (Expr.toPolyK a).beq' (Expr.toPolyK b) = true) :
    a.denote ctx = b.denote ctx := by
  have h' : Expr.toPolyK a = Expr.toPolyK b := by simpa using h
  rw [← Expr.denote_toPolyK ctx a, ← Expr.denote_toPolyK ctx b, h']

end AvgRS.RingKernel

end
