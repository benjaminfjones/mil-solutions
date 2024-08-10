import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MilSolutions.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu  -- ∪ is defined as a disjunction
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  rcases hx with hxt | hxu
  case inl =>
    exact ⟨ hxt.1, Or.inl hxt.2 ⟩
  case inr =>
    exact ⟨ hxu.1, Or.inr hxu.2 ⟩

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  show False

  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · exact xnt xt
  · exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  -- use xs  -- equivalent to refine ⟨ xs, ?_ ⟩

  -- Using `refine`:
  -- the placeholders ?_ are not unified, but extracted into new goals
  refine ⟨ xs, ?_ ⟩
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨ hxs, hxntu ⟩
  constructor
  constructor
  assumption
  intro ht
  exact hxntu (Or.inl ht)
  intro hu
  exact hxntu (Or.inr hu)
  -- Proof automation also works!
  -- `aesop` finds:
  -- simp_all only [mem_union, not_or, mem_diff, not_false_eq_true, and_self]

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm
      (fun _x ⟨ xs, xt ⟩ => ⟨ xt, xs ⟩)
      (fun _x ⟨ xt, xs ⟩ => ⟨ xs, xt ⟩)

example : s ∩ (s ∪ t) = s :=
  Set.ext fun _x ↦ ⟨fun ⟨xs, _⟩ ↦ xs, fun xs ↦ ⟨xs, Or.inl xs⟩⟩

example : s ∪ s ∩ t = s := by
  ext
  constructor
  · rintro (hxs | hxst)
    · assumption
    · exact hxst.1
  · rintro hxs
    exact Or.inl hxs

example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · rintro (⟨hxs, _⟩ | hxt)
    · exact Or.inl hxs
    · exact Or.inr hxt
  · rintro (hxs | hxt)
    -- any other way than splitting on x ∈ t ?
    · by_cases ht : x ∈ t
      · exact Or.inr ht
      · exact Or.inl ⟨hxs, ht⟩
    · exact Or.inr hxt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  -- aesop + simplifications
  · intro a
    simp_all only [mem_union, mem_diff, mem_inter_iff, not_and]
    cases a with
    | inl h => simp_all only [or_false, not_false_eq_true, imp_self, and_self]
    | inr h_1 => simp_all only [or_true, not_true_eq_false, false_implies, and_self]
  · intro ⟨hleft, hright⟩
    simp_all only [mem_diff, mem_union, mem_inter_iff, not_and]
    cases hleft with
    | inl h => simp_all only [true_implies, not_false_eq_true, and_self, not_true_eq_false, or_false]
    | inr h_1 => simp_all only [not_true_eq_false, imp_false, and_self, not_false_eq_true, or_true]

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  -- rw [evens, odds]
  ext n
  simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro a ha
  simp only [mem_inter_iff, mem_setOf_eq] at *
  intro hne
  rcases Nat.Prime.eq_two_or_odd ha.1 with (h2 | hodd)
  · exact (Nat.ne_of_gt ha.2) h2
  · have : a % 2 = 0 := Nat.even_iff.mp hne
    exact one_ne_zero (Eq.trans hodd.symm this)

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

-- Bounded quantifiers notation: `∀ x ∈ S, ...` and `∃ x ∈ S, ...`
--
-- Note: theorems with `ball_...` or `bex_...` stand for "bounded all", "bounded exists"
#check bex_congr

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · exact h₀ x (ssubt xs)
  exact h₁ x (ssubt xs)

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, hxs, _, hpx⟩
  use x
  exact ⟨ssubt hxs, hpx⟩

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)  -- indexed family of sets A_i, B_i
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (xs | xAi)
    · intro
      exact Or.inr xs
    intro i
    exact Or.inl (xAi i)
  -- ← requires classical logic
  intro h
  by_cases xs : x ∈ s
  · exact Or.inl xs
  right
  intro i
  rcases h i
  · assumption
  contradiction


def primes : Set ℕ :=
  { x | Nat.Prime x }

-- These examples are hard to read: | is different than ∣
example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  -- simp
  -- alternatively:
  -- don't exactly understand `exists_prop`. "Exists a proof of a, s.t. b holds ↔ a ∧ b"?
  simp only [mem_setOf_eq, exists_prop]

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  -- simp
  simp only [mem_iUnion, mem_setOf_eq, exists_prop]

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  rw [eq_univ_iff_forall]
  intro x
  simp only [mem_iUnion₂, exists_prop]
  rcases Nat.exists_infinite_primes x with ⟨q, hxq, hq'⟩
  use q
  exact ⟨hq', hxq⟩


end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
