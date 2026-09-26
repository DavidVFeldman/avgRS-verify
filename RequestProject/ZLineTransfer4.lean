module

public import RequestProject.ZLineTransfer3
public import RequestProject.ZLineAlgBase

@[expose] public section

/-!
# The z-line resolvent: the limit scalars form a `ZAlgData`

The `X`-adic limits of the truncated scalars satisfy all the identities bundled in
`ZAlgData t w`: every truncated identity (exact, or up to an error divisible by `X ^ m`) passes
to the limit.
-/

namespace AvgRS

open Finset PowerSeries Matrix Formal

section Limits

variable (t w : ℚ)

noncomputable def zlP : ℚ⟦X⟧ := xlim fun n => Pzz t w (n + 2)
noncomputable def zlPh : ℚ⟦X⟧ := xlim fun n => Phzz t w (n + 2)
noncomputable def zlQ : ℚ⟦X⟧ := xlim fun n => Qzz t w (n + 2)
noncomputable def zlP1 : ℚ⟦X⟧ := xlim fun n => P1zz t w (n + 2)
noncomputable def zlPh1 : ℚ⟦X⟧ := xlim fun n => Ph1zz t w (n + 2)
noncomputable def zlQ1 : ℚ⟦X⟧ := xlim fun n => Q1zz t w (n + 2)
noncomputable def zlQh1 : ℚ⟦X⟧ := xlim fun n => Qh1zz t w (n + 2)
noncomputable def zlp0 : ℚ⟦X⟧ := xlim fun n => pzz t w (n + 2) 0
noncomputable def zlq0 : ℚ⟦X⟧ := xlim fun n => qzz t w (n + 2) 0
noncomputable def zlp1 : ℚ⟦X⟧ := xlim fun n => pzz t w (n + 2) 1
noncomputable def zlq1 : ℚ⟦X⟧ := xlim fun n => qzz t w (n + 2) 1
noncomputable def zlG00 : ℚ⟦X⟧ := xlim fun n => Gzz t w (n + 2) 0 0
noncomputable def zlG01 : ℚ⟦X⟧ := xlim fun n => Gzz t w (n + 2) 0 1
noncomputable def zlG10 : ℚ⟦X⟧ := xlim fun n => Gzz t w (n + 2) 1 0
noncomputable def zlG11 : ℚ⟦X⟧ := xlim fun n => Gzz t w (n + 2) 1 1
/-- The limit of `det(1 + ω C₁)`. -/
noncomputable def zlD : ℚ⟦X⟧ := xlim fun n => (Bg w (lamW t) (muW t) (n + 2)).det
/-- The limit of `det(1 + Ω C₁)`, `Ω = diag(1, 1, ω, ω, …)`. -/
noncomputable def zlDZ : ℚ⟦X⟧ := xlim fun n => (1 + Zm ℚ (n + 2) w * Cg (lamW t) (muW t) (n + 2)).det

lemma isLim_zlP : IsLim (fun n => Pzz t w (n + 2)) (zlP t w) := isLim_xlim fun _ => Pg_succ
lemma isLim_zlPh : IsLim (fun n => Phzz t w (n + 2)) (zlPh t w) := isLim_xlim fun _ => Pg_succ
lemma isLim_zlQ : IsLim (fun n => Qzz t w (n + 2)) (zlQ t w) := isLim_xlim fun _ => Qg_succ
lemma isLim_zlP1 : IsLim (fun n => P1zz t w (n + 2)) (zlP1 t w) := isLim_xlim fun _ => P1g_succ
lemma isLim_zlPh1 : IsLim (fun n => Ph1zz t w (n + 2)) (zlPh1 t w) :=
  isLim_xlim fun _ => P1g_succ
lemma isLim_zlQ1 : IsLim (fun n => Q1zz t w (n + 2)) (zlQ1 t w) := isLim_xlim fun _ => Q1g_succ
lemma isLim_zlQh1 : IsLim (fun n => Qh1zz t w (n + 2)) (zlQh1 t w) :=
  isLim_xlim fun _ => Q1g_succ
lemma isLim_zlp0 : IsLim (fun n => pzz t w (n + 2) 0) (zlp0 t w) :=
  isLim_xlim fun n => by simpa using pg_succ_apply (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 0
lemma isLim_zlq0 : IsLim (fun n => qzz t w (n + 2) 0) (zlq0 t w) :=
  isLim_xlim fun n => by simpa using qg_succ_apply (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 0
lemma isLim_zlp1 : IsLim (fun n => pzz t w (n + 2) 1) (zlp1 t w) :=
  isLim_xlim fun n => by
    simpa [castSucc_one'] using pg_succ_apply (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 1
lemma isLim_zlq1 : IsLim (fun n => qzz t w (n + 2) 1) (zlq1 t w) :=
  isLim_xlim fun n => by
    simpa [castSucc_one'] using qg_succ_apply (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 1
lemma isLim_zlG00 : IsLim (fun n => Gzz t w (n + 2) 0 0) (zlG00 t w) :=
  isLim_xlim fun n => by
    simpa using Gg_succ_apply (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 0 0
lemma isLim_zlG01 : IsLim (fun n => Gzz t w (n + 2) 0 1) (zlG01 t w) :=
  isLim_xlim fun n => by
    simpa [castSucc_one'] using Gg_succ_apply (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 0 1
lemma isLim_zlG10 : IsLim (fun n => Gzz t w (n + 2) 1 0) (zlG10 t w) :=
  isLim_xlim fun n => by
    simpa [castSucc_one'] using Gg_succ_apply (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 1 0
lemma isLim_zlG11 : IsLim (fun n => Gzz t w (n + 2) 1 1) (zlG11 t w) :=
  isLim_xlim fun n => by
    simpa [castSucc_one'] using Gg_succ_apply (w := w) (l := lamW t) (μ := muW t) (m := n + 2) 1 1
lemma isLim_zlD : IsLim (fun n => (Bg w (lamW t) (muW t) (n + 2)).det) (zlD t w) :=
  isLim_xlim fun _ => detBg_succ
lemma isLim_zlDZ :
    IsLim (fun n => (1 + Zm ℚ (n + 2) w * Cg (lamW t) (muW t) (n + 2)).det) (zlDZ t w) :=
  isLim_xlim fun _ => detZg_succ

end Limits

/-- Prove `IsLim` of a polynomial expression in the base sequences. -/
macro "zislim" : tactic => `(tactic| repeat' (with_reducible_and_instances first
  | exact isLim_zlP _ _ | exact isLim_zlPh _ _ | exact isLim_zlQ _ _ | exact isLim_zlP1 _ _
  | exact isLim_zlPh1 _ _ | exact isLim_zlQ1 _ _ | exact isLim_zlQh1 _ _
  | exact isLim_zlp0 _ _ | exact isLim_zlq0 _ _ | exact isLim_zlp1 _ _ | exact isLim_zlq1 _ _
  | exact isLim_zlG00 _ _ | exact isLim_zlG01 _ _ | exact isLim_zlG10 _ _ | exact isLim_zlG11 _ _
  | exact isLim_zlD _ _ | exact isLim_zlDZ _ _
  | apply IsLim.add | apply IsLim.sub | apply IsLim.mul | apply IsLim.neg | apply IsLim.pow
  | apply IsLim.deriv
  | exact IsLim.const _))

lemma dvd_of_eq' {a b : ℚ⟦X⟧} (h : a = b) (k : ℕ) : (X : ℚ⟦X⟧) ^ k ∣ a - b := by
  rw [h, sub_self]; exact dvd_zero _

lemma dvd_of_eq_err {a b e : ℚ⟦X⟧} {k k' : ℕ} (h : a = b + e) (he : (X : ℚ⟦X⟧) ^ k' ∣ e)
    (hk : k ≤ k') : (X : ℚ⟦X⟧) ^ k ∣ a - b := by
  rw [h, add_sub_cancel_left]; exact (pow_dvd_pow _ hk).trans he

end AvgRS
