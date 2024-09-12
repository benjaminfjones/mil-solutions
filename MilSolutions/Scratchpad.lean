import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Mark
open Finset
def Address := Finset.range 1024

example : 0 ∈ Address := by
  unfold Address
  rw [mem_range]
  simp only [Nat.zero_lt_succ]

end Mark

namespace Sean

#check beq_iff_eq

variable (α : Type)
example (e f: α) [BEq α] [LawfulBEq α]: (e == f) = true ↔ e = f := by
  exact beq_iff_eq e f

end Sean

namespace Fermat
-- import Mathlib.Algebra.BigOperators.Group.Finset
-- import Mathlib.Data.Finset.Basic
-- import Mathlib.Tactic

open Finset

def Fermat (n : Nat) : Nat := 2^(2^n) + 1

#check Finset.prod

theorem FermatRecurrence {n : Nat} : Finset.prod (range (n+1)) (fun i => Fermat i) = Fermat (n+1) - 2 := by
  induction' n with k ih
  · simp only [zero_add, range_one, prod_singleton]
    unfold Fermat
    norm_num
  · -- use relationship b/w range (k+1) and range (k + 1 + 1)
    sorry

theorem FermatRecurrence' {n : Nat} : ∏ i ∈ range (n+1), Fermat i = Fermat (n+1) - 2 := by
  sorry

end Fermat

namespace SumSyntax

open BigOperators

structure Vector (n: Nat) where
  V : Fin n → ℝ

-- sum0 isn't well-formed. The sum syntax requires a pattern (function) (bound_arg)
-- def sum0 (n: Nat) (v: Vector n) : Real := ∑ i, (fun i => v.V i)
def sum1 (n: Nat) (v: Vector n) : Real := ∑ i, v.V i
def sum2 (n: Nat) (v: Vector n) : Real := Finset.sum Finset.univ (fun i => v.V i)

end SumSyntax
