import Mathlib.Data.Nat.GCD.Basic
import MilSolutions.Common

example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right

theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · rw [fac]
    norm_num
  · induction' n with m ih
    · rw [zero_add, fac, fac]
      norm_num
    rw [fac]
    have pow_eq : 2^(m + 1 + 1 - 1) = 2 * 2^(m + 1 - 1) := by
      calc
        2^(m + 1 + 1 - 1) = 2^(1 + m + 1 - 1) := by rw [add_comm, add_assoc]
        _                 = 2 * 2^(m + 1 - 1) := by
                                                   simp only [add_tsub_cancel_right]
                                                   ring
    have m2 : 2 ≤ m + 1 + 1 := by norm_num
    rw [pow_eq]
    exact Nat.mul_le_mul m2 ih


section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x in range n.succ, f x = ∑ x in range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
  Finset.prod_range_succ f n

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction' n with n ih
  · rw [fac, prod_range_zero]
  rw [fac, ih, prod_range_succ, mul_comm]

example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp only [zero_add, mul_one, range_one, sum_singleton, mul_zero]
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  induction' n with n ih
  · rw [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [Finset.sum_range_succ]
  nth_rw 4 [mul_add]
  rw [← ih]
  ring

end

inductive MyNat
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | _, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [succ_add, add, succ_add, ih]
  rfl

theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
  induction' k with k ih
  · rw [mul, add, add]
  rw [add, mul, mul, ← add_assoc, ih]

theorem zero_mul (n : MyNat) : mul zero n = zero := by
  induction' n with n ih
  · rw [mul]
  rw [mul, add_comm, zero_add, ih]

theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
  induction' n with n ih
  · rw [mul, mul, zero_add]
  -- ih: (m+1) * n = m * n + n
  -- ⊢ (m+1) * (n+1) = m * (n+1) + (n+1)
  rw [mul, mul]
  -- ⊢ (m+1) * n + (m+1) = ((m*n + m) + (n+1))
  rw [ih]
  -- ⊢ (m*n + n) + (m+1) = ((m*n + m) + (n+1))
  rw [add, add]
  rw [succ.injEq]
  -- ⊢ (m*n + n) + m = (m*n = m) + n
  rw [add_assoc, add_assoc, add_comm m n]

theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
  induction' n with n ih
  · rw [mul, zero_mul]
  rw [mul, ih, succ_mul]

end MyNat
