import Mathlib.Data.Nat.Prime.Basic
import MilSolutions.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (_h0 : m ≠ 0) (_h1 : m ≠ 1) : 2 ≤ m :=
  -- cases m
  -- case zero => contradiction
  -- case succ m =>
  match m with
    | 0 => by contradiction
    | Nat.succ m => by
        cases m; contradiction
        repeat' apply Nat.succ_le_succ
        apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    -- find contradiction from `m = 0 ∧ 2 ≤ m`
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

theorem not_dvd_one_of_prime : ∀ p, Nat.Prime p → ¬ p ∣ 1 := by
  intro p pp pdvd
  rcases pdvd with ⟨k, hk⟩
  have pge2 : 2 ≤ p := (Nat.prime_def_lt.mp pp).1
  have : p = 1 := eq_one_of_mul_right hk.symm
  rw [this] at pge2
  contradiction  -- 2 ≤ 1

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n

  -- using a prime factor of `n + 1` saves us from considering the case of
  -- `n = 0` separately
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    apply Nat.succ_le_succ
    rw [Nat.factorial]
    refine Nat.one_le_iff_ne_zero.mpr ?_
    apply mul_ne_zero
    · exact Nat.succ_ne_zero n
    exact ne_zero_of_lt (Nat.factorial_pos n)
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩

  show p > n
  by_contra ple
  push_neg at ple
  have pge2 : 2 ≤ p := (Nat.prime_def_lt.mp pp).1
  have : p ∣ Nat.factorial (n + 1) := by
    apply Nat.dvd_factorial
    . exact Nat.zero_lt_one.trans (Nat.lt_of_succ_le pge2)
    exact ple.trans (Nat.le_succ n)
  have : p ∣ 1 := by
    exact (Nat.dvd_add_iff_right this).mpr pdvd
  exact not_dvd_one_of_prime p pp this

open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext
  simp only [mem_inter, mem_union]
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext
  simp only [mem_sdiff, mem_union, not_or]
  tauto

end

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  rcases Nat.Prime.eq_one_or_self_of_dvd prime_q _ h with h1 | hpq
  . exfalso
    have : 2 ≤ p := by apply (Nat.prime_def_lt.mp prime_p).1
    rw [h1] at this
    contradiction
  assumption

theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp only [prod_empty, Nat.dvd_one] at h₁
    -- inline: p prime ∧ p = 1 → False
    exfalso
    have : 2 ≤ p := by apply (Nat.prime_def_lt.mp prime_p).1
    rw [h₁] at this
    contradiction
    -- linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
  rcases h₁ with pda | pdprod
  . exact Or.inl  (Nat.Prime.eq_of_dvd_of_prime prime_p h₀.1 pda)
  . apply Or.inr
    exact ih h₀.2 pdprod

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

/-
useful below

⊢ ∀ {ι : Type u_1} {R : Type u_2} [inst : CommMonoidWithZero R] [inst_1 : PartialOrder R] [inst_2 : ZeroLEOneClass R]
  [inst_3 : PosMulStrictMono R] [inst_4 : Nontrivial R] {f : ι → R} {s : Finset ι},
  (∀ i ∈ s, 0 < f i) → 0 < ∏ i ∈ s, f i
-/
#check prod_pos

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg  at h
  -- bind `s'` and record the definitional equality
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp only [s'_def, mem_filter, and_iff_right_iff_imp]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := by
    apply Nat.succ_le_succ
    apply Nat.one_le_of_lt
    refine prod_pos ?_
    intro i is'
    exact lt_of_lt_of_le zero_lt_two (Nat.prime_def_lt.mp (mem_s'.mp is')).1
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i in s', i := by
    apply dvd_prod_of_mem
    exact mem_s'.mpr pp
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp only [add_tsub_cancel_left]
  show False
  exact not_dvd_one_of_prime p pp this

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id  -- change the goal to def. equal version involving `id`
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp only [mem_filter, mem_range, Nat.lt_succ_iff, iff_and_self]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)  -- to make `interval_cases` effective
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  -- all but case 2 < 4 are closed, disjunctions are simpflied to one junct
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  -- every case below is False → False
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

-- a simpler, stronger version of above that doesn't depend on `two_le`
theorem three_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 3 ≤ n := by
  by_contra hh
  push_neg at hh
  interval_cases n <;> contradiction

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  sorry

theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg  at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  . sorry
  . sorry
example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg  at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i in erase s 3, i) + 3) % 4 = 3 := by
    sorry
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    sorry
  have pne3 : p ≠ 3 := by
    sorry
  have : p ∣ 4 * ∏ i in erase s 3, i := by
    sorry
  have : p ∣ 3 := by
    sorry
  have : p = 3 := by
    sorry
  contradiction
