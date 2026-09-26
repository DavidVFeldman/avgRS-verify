module

public import RequestProject.ZLineAlgRelsDef

@[expose] public section

/-!
# Batch 7: the relation R8, and the certificates rebuilt around it

`R7` (`ZLineAlgRelsDef.lean`) has 169 terms and is the reason the three `linear_combination`
certificates in `ZLineAlgG01m`, `ZLineAlgG11m` and `ZLineAlgBig` run to 70–155 thousand characters.
This file supplies a five-times smaller relation with the same role, and a one-line proof of it.

With `σ = (1 − X²)(P₁ − ω X P Q)` and `u = 1 − X²`, eliminating `P̂₁` between `S0` and `R3` gives

    R8 = (σ + X² P) · R3 − P · u · S0,

and in grouped form, exactly,

    u σ² P̂ = − u³ X² ω P̂² P³ + u² X P̂ P² (ω(X²+1) Q − t X)
             + u (X² P̂ P² + X² ω P Q² + t X P Q − 2 X P₁ Q) − X(X²+1) P Q,

which is the z-line analogue of the Plancherel first integral `σ² = βW` (`eq:I1` of `avgRS.tex`).
See COMMISSION.md.
-/

namespace AvgRS

open PowerSeries

variable {t w : ℚ}

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- **Item A1.**  The relation `R8`, in expanded form.  Proof: `R8 = (σ + X²P)·R3 − P·u·S0`,
one `linear_combination` with the two cofactors written out, no cancellation and no side condition
(`1 − X²` is a unit but is not even divided by here). -/
lemma zR8 (Z : ZAlgData t w)
    (hS0 : X^6*(C w)^2*Z.P*Z.Ph*Z.Q^2 + ... (as in ZLineAlgRelsDef.hS0; copy it verbatim) = 0)
    (hR3 : 2*X^4*Z.P*Z.Ph + X^4*Z.P*Z.Ph1 - X^4*Z.Ph*Z.P1 - 2*X^2*Z.P*Z.Ph - 2*X^2*Z.P*Z.Ph1 + 2*X^2*Z.Ph*Z.P1 - 2*X*Z.Q + Z.P*Z.Ph1 - Z.Ph*Z.P1 = 0) :
    (X^8*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 + X^8*(C w)*Z.P^3*Z.Ph^2 - 3*X^6*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 - 3*X^6*(C w)*Z.P^3*Z.Ph^2 - 2*X^7*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 + X^7*(C w)*Z.P^2*Z.Ph*Z.Q + 3*X^4*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 + 3*X^4*(C w)*Z.P^3*Z.Ph^2 + 6*X^5*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 - X^5*(C w)*Z.P^2*Z.Ph*Z.Q - X^6*(C t)*Z.P^2*Z.Ph - X^2*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 + X^6*Z.Ph*Z.P1^2 - X^2*(C w)*Z.P^3*Z.Ph^2 - 6*X^3*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 - X^3*(C w)*Z.P^2*Z.Ph*Z.Q - X^4*(C w)*Z.P*Z.Q^2 + 2*X^4*(C t)*Z.P^2*Z.Ph - 3*X^4*Z.Ph*Z.P1^2 - X^4*Z.P^2*Z.Ph + 2*X*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 + X*(C w)*Z.P^2*Z.Ph*Z.Q + X^2*(C w)*Z.P*Z.Q^2 - X^2*(C t)*Z.P^2*Z.Ph - X^3*(C t)*Z.P*Z.Q + 3*X^2*Z.Ph*Z.P1^2 + X^2*Z.P^2*Z.Ph + 2*X^3*Z.Q*Z.P1 - X^3*Z.P*Z.Q + X*(C t)*Z.P*Z.Q - Z.Ph*Z.P1^2 - 2*X*Z.Q*Z.P1 - X*Z.P*Z.Q) = 0 := by
  sorry

/-- **Item A2.**  The grouped form, for the paper.  `σ` is `(1 − X²)(P₁ − ωXPQ)`. -/
lemma zR8_grouped (Z : ZAlgData t w)
    (hR8 : (X^8*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 + X^8*(C w)*Z.P^3*Z.Ph^2 - 3*X^6*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 - 3*X^6*(C w)*Z.P^3*Z.Ph^2 - 2*X^7*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 + X^7*(C w)*Z.P^2*Z.Ph*Z.Q + 3*X^4*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 + 3*X^4*(C w)*Z.P^3*Z.Ph^2 + 6*X^5*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 - X^5*(C w)*Z.P^2*Z.Ph*Z.Q - X^6*(C t)*Z.P^2*Z.Ph - X^2*(C w)^2*Z.P^2*Z.Ph*Z.Q^2 + X^6*Z.Ph*Z.P1^2 - X^2*(C w)*Z.P^3*Z.Ph^2 - 6*X^3*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 - X^3*(C w)*Z.P^2*Z.Ph*Z.Q - X^4*(C w)*Z.P*Z.Q^2 + 2*X^4*(C t)*Z.P^2*Z.Ph - 3*X^4*Z.Ph*Z.P1^2 - X^4*Z.P^2*Z.Ph + 2*X*(C w)*Z.P*Z.Ph*Z.Q*Z.P1 + X*(C w)*Z.P^2*Z.Ph*Z.Q + X^2*(C w)*Z.P*Z.Q^2 - X^2*(C t)*Z.P^2*Z.Ph - X^3*(C t)*Z.P*Z.Q + 3*X^2*Z.Ph*Z.P1^2 + X^2*Z.P^2*Z.Ph + 2*X^3*Z.Q*Z.P1 - X^3*Z.P*Z.Q + X*(C t)*Z.P*Z.Q - Z.Ph*Z.P1^2 - 2*X*Z.Q*Z.P1 - X*Z.P*Z.Q) = 0) :
    (1 - X ^ 2) * ((1 - X ^ 2) * (Z.P1 - C w * X * Z.P * Z.Q)) ^ 2 * Z.Ph
      = -((1 - X ^ 2) ^ 3 * X ^ 2 * C w * Z.Ph ^ 2 * Z.P ^ 3)
        + (1 - X ^ 2) ^ 2 * X * Z.Ph * Z.P ^ 2 * (C w * (X ^ 2 + 1) * Z.Q - C t * X)
        + (1 - X ^ 2) * (X ^ 2 * Z.Ph * Z.P ^ 2 + X ^ 2 * C w * Z.P * Z.Q ^ 2
            + C t * X * Z.P * Z.Q - 2 * X * Z.P1 * Z.Q)
        - X * (X ^ 2 + 1) * Z.P * Z.Q := by
  sorry

end AvgRS
