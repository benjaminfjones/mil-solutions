import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import MilSolutions.Common

open Set
open Function

noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]

section
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n

-- On `sbSet`, `sbFun` is defined to be `f`, on the compliment it is `invFun g`
def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    exact ⟨trivial, hx⟩
  have : ∃ y, g y = x := by
    rcases this with ⟨x', hx'⟩
    exact ⟨x', hx'.2⟩
  exact invFun_eq this

theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  intro (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    -- this bullet shows that `x1 = x2` in the `x2 ∈ A` case by symmetry
    -- if we know the `x1 ∈ A` case
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        rw [hxeq]
        rw [A_def] at x₂nA
        symm
        exact @sb_right_inv _ _ _ f g x₂ x₂nA  -- why???
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
    have : f x₁ = f x₂ := by rwa [if_pos x₁A, if_pos x₂A] at *
    exact hf this
  push_neg at xA
  rw [if_neg xA.1, if_neg xA.2] at hxeq
  have : g (invFun g x₁) = g (invFun g x₂) := hxeq ▸ Eq.refl (g (invFun g x₁))
  rw [A_def] at xA
  rwa [@sb_right_inv _ _ _ f g x₁ xA.1, @sb_right_inv _ _ _ f g x₂ xA.2] at this

theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with Nat.zero | n
    · simp only [sbAux, image_univ, mem_diff, mem_univ, mem_range, exists_apply_eq_apply,
      not_true_eq_false, and_false] at hn
    simp only [sbAux, mem_image, exists_exists_and_eq_and] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    simp only [h_def, sbFun, if_pos this]
    exact hg hx
  use g y
  rw [h_def, sbFun, if_neg gyA]
  exact leftInverse_invFun hg y

end

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩

-- Auxiliary information
section
variable (g : β → α) (x : α)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

end
