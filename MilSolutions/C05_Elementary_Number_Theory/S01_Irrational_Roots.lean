import MilSolutions.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

-- Three equivalent formalizations of primality for `Nat`:
-- 1. `Nat.Prime`
-- 2. `Nat.prime_def_lt`
-- 3. `Nat.Prime.eq_one_or_self_of_dvd`

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul  -- Irreducibility
#check Nat.Prime.dvd_mul Nat.prime_two  -- metavariables left... ?
#check Nat.prime_two.dvd_mul            -- metavariables left... ?

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  -- h : 2 | m ∨ 2 | m
  cases h <;> assumption

-- Generalize the above
theorem dvdp_of_dvdp_sqr {m p: ℕ} (prime_p: p.Prime) (h : p ∣ m^2) : p ∣ m := by
  rw [pow_two, prime_p.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (by use n^2)
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=
    (mul_right_inj' (by norm_num)).mp this
  have : 2 ∣ n := by
    apply even_of_even_sqr
    exact ⟨k^2, this.symm⟩
  have : 2 ∣ m.gcd n := by
    apply dvd_gcd <;> assumption
  have : 2 ∣ 1 := by
    rw [coprime_mn] at this
    assumption
  norm_num at this

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have : p ∣ m := Nat.Prime.dvd_of_dvd_pow prime_p (by use n^2)
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 :=
    (mul_right_inj' prime_p.ne_zero).mp this
  have : p ∣ n := by
    apply dvdp_of_dvdp_sqr
    assumption
    exact ⟨k^2, this.symm⟩
  have : p ∣ m.gcd n := by
    apply dvd_gcd <;> assumption
  have hp1 : p ∣ 1 := by
    rw [coprime_mn] at this
    assumption
  norm_num at hp1
  have : 2 ≤ 1 := hp1 ▸ (Nat.prime_def_lt.mp prime_p).1
  contradiction


#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique


theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    exact factorization_pow' m 2 p
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [@factorization_mul' p (n^2) prime_p.ne_zero nsqr_nez p]
    rw [Nat.Prime.factorization' prime_p]
    rw [factorization_pow' n 2 p]
    ring
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  -- have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have npow_nz : n ^ k ≠ 0 := by
    intro nkz
    obtain nz : n = 0 := pow_eq_zero nkz
    exact nnz nz
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    apply factorization_pow'
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    rw [factorization_mul' (Nat.succ_ne_zero r) npow_nz]
    rw [factorization_pow']
    ring
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm]
    rw [Nat.add_sub_cancel]  -- implicitly invokes (def?) `1.factorization p = 0`
  rw [this]
  -- use m.factorization p - n.factorization p ... leads to subtraction identity to prove
  apply Nat.dvd_sub'
  use m.factorization p
  use n.factorization p


#check multiplicity
