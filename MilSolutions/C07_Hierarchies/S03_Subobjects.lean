import MilSolutions.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  /- coe : Submonoid₁ M → Set M -/
  coe := Submonoid₁.carrier
  /- coe_injective' : ∀ (x x_1 : Submonoid₁ M), x.carrier = x_1.carrier → x = x_1 -/
  coe_injective' _ _ := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) : Set α := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z ⟨w1, w1N, z1, z1N, he1⟩ ⟨w2, w2N, z2, z2N, he2⟩
      use (w1 * w2)
      constructor
      · exact (mul_mem w1N w2N)
      rw [← mul_assoc, he1, mul_assoc, mul_comm z1 _, ← mul_assoc, he2, mul_assoc]
      use (z2 * z1)
      constructor
      · exact (mul_mem z2N z1N)
      rfl
  }

-- Provide a function mapping the subobject to the equivalence relation under
-- which quotients can be taken.
instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  /- quotient' : Submonoid M → Type u_1 -/
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

/-
Quotient.surjective_Quotient_mk''.{u_1} {α : Sort u_1} {s₁ : Setoid α} : Function.Surjective Quotient.mk''
-/
#check Quotient.surjective_Quotient_mk''
/-
def Function.Surjective.{u₁, u₂} : {α : Sort u₁} → {β : Sort u₂} → (α → β) → Prop :=
fun {α} {β} f => ∀ (b : β), ∃ a, f a = b
-/
-- #print Function.Surjective
lemma quotient_map_surjective [CommMonoid M] (N : Submonoid M) : Function.Surjective (QuotientMonoid.mk N) := by
  apply Quotient.surjective_Quotient_mk''

instance [CommMonoid M] : Std.Associative (α := M) (· * · ) where
  assoc := mul_assoc

instance [CommMonoid M] : Std.Commutative (α := M) (· * · ) where
  comm := mul_comm

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      simp only [Relator.LiftFun]  -- removes the confusing ⇒ notation
      intro a b hab c d hcd
      -- hab: Setoid.r a b := ∃ w1 ∈ N, ∃ z1 ∈ N, a*w1 = b*z1
      let ⟨w1, w1N, z1, z1N, haw1_bz1⟩ := hab
      -- hcd: Setoid.r c d := ∃ w ∈ N, ∃ z ∈ N, c*w = d*z
      let ⟨w2, w2N, z2, z2N, hcw2_dz2⟩ := hcd

      -- rephrase Setoid.r (a*c) (b*d)
      show ∃ w ∈ N, ∃ z ∈ N, (a*c)*w = (b*d)*z
      -- (a*c)*w1*w2 = (a*w1)*c*w2 = (b*z1)*c*w2 = b*z1*(c*w2) = b*z1*d*z2 = (b*d)*(z1*z2)
      use (w1*w2); constructor; exact Submonoid.mul_mem N w1N w2N
      use (z1*z2); constructor; exact Submonoid.mul_mem N z1N z2N
      rw [← mul_assoc _ w1 w2, mul_assoc a c _, mul_comm c _, ← mul_assoc a w1 _, haw1_bz1]
      rw [mul_assoc _ _ w2, hcw2_dz2]
      ac_rfl
  )
  mul_assoc := by
      -- If f : M -> M ⧸ N is the quotient surjection, then ∀ a ∈ M ⧸ N, ∃ a' ∈ M, f a' = a.
      -- thus a*b*c = a*(b*c) ↔ f a' * f b' * f c' = f a' * (f b' * f c')
      -- which follows from Monoid.mul_assoc **after** lifting `*` via f.
      intro a b c
      have : ∃ a' ∈ M, QuotientMonoid.mk N a' = a := by sorry
  one := QuotientMonoid.mk N 1
  one_mul := by
      sorry
  mul_one := by
      sorry

#check Quotient.mk
