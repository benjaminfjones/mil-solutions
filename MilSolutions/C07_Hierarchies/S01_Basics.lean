import MilSolutions.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit true


/-- Instances of this class have a special element denoted by `one`. There is
    no other structure beyond that. -/
class One₁ (α : Type) where
  /-- The element one -/
  one : α


-- The instance parameter on `One₁.one` is implicit
#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

-- The instance parameter on `One₂.one` is explicit now
#check One₂.one  -- One₂.one {α : Type} (self : One₂ α) : α


-- resolve stuck metavariable inference with an initial type annotation
-- note: [One₁.one] is silly here because it only matters when the delcaration
--   is used and an example cannot be used.
example (α : Type) [One₁ α] : α := One₁.one
-- resolve stuck metavariable inference with a final type annotation
example (α : Type) [One₁ α] := (One₁.one : α)

@[inherit_doc]  -- use docs of One₁.one for 𝟙 (slash b1)
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl


-- a binary operator "diamond"
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia


class Semigroup₁ (α : Type) where
  -- `toDia₁` is in local context here, but the instance does not become part
  -- of the type class database
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)


-- Add Dia₁ instance to Semigroup₁. This allows the following line to typecheck
attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b

-- 𝟙    -- slash b1
-- ⋄    -- slash diamond
-- ◇    -- slash Diamond
-- ◇    -- slash diw

-- Some kind of rendering bug occurs here: https://github.com/leanprover/vscode-lean4/issues/555
-- 𝟙 ⋄  -- slash b1 space slash diamond
-- 1 ⋄  -- 1 space slash diamond
-- ⋄ 𝟙
-- ⋄ 1
-- 𝟚 ⋄
-- 2 ⋄
-- 𝟙 1


class Semigroup₂ (α : Type) extends Dia₁ α where
  -- Note: Now, `toDia₁` is both in local context, and the instance becomes part
  -- of the type class database!

  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a



set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙


class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α


class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α


example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl


/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

-- Note: `Monoid₁`, as an extension-only class has a constructor that includes only the
--   "disjoint" parts of the classes it extends. A `toDiaOneClass₁` field is auto-generated
--   to provide a symmetrical view to the user.
/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk


#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁


class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙


lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]


-- Makes `one_dia` etc part of the root namespace
export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)


example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]


lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
  left_inv_eq_right_inv₁ (inv_dia a : a⁻¹ ⋄ a = 𝟙) h

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  have hai : (a⁻¹)⁻¹ ⋄ a⁻¹ = 𝟙 := inv_dia (a⁻¹)
  have hia : a⁻¹ ⋄ a = 𝟙 := inv_dia a
  have : (a⁻¹)⁻¹ = a := left_inv_eq_right_inv₁ hai hia
  rwa [this] at hai


class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

-- tells the to_additive mechanism to use existing `AddSemigroup₃` for the
-- additive version
@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

-- whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]
attribute [aesop unsafe 10% apply] left_inv_eq_right_inv' left_neg_eq_right_neg'

#check left_neg_eq_right_neg'

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1


attribute [simp] Group₃.inv_mul AddGroup₃.neg_add



@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  apply left_inv_eq_right_inv'
  exact Group₃.inv_mul a
  assumption

@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  -- same proof as `dia_inv`, replacing ⋄ with * and `inv_dia` with `inv_mul`
  have hai : (a⁻¹)⁻¹ * a⁻¹ = 1 := inv_mul (a⁻¹)
  have hia : a⁻¹ * a = 1 := inv_mul a
  have : (a⁻¹)⁻¹ = a := left_inv_eq_right_inv' hai hia
  rwa [this] at hai

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  calc
    b = 1 * b := by rw [one_mul b]
    _ = (a⁻¹ * a) * b := by rw [Group₃.inv_mul a]    -- or simp
    _ = a⁻¹ * (a * b) := by rw [mul_assoc₃ a⁻¹ a b]  -- simp makes no progress
    _ = a⁻¹ * (a * c) := by rw [h]                   -- or simp [h]
    _ = (a⁻¹ * a) * c := by rw [← mul_assoc₃ a⁻¹ a c]
    _ = 1 * c := by rw [← Group₃.inv_mul a]
    _ = c := by rw [one_mul c]

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
  calc
    b = b * 1 := by rw [mul_one b]
    _ = b * (a * a⁻¹) := by simp only [mul_one, Group₃.mul_inv]
    _ = (b * a) * a⁻¹ := by simp [mul_assoc₃]
    _ = (c * a) * a⁻¹ := by rw [h]
    _ = c * (a * a⁻¹) := by simp [mul_assoc₃]
    _ = c * 1 := by simp only [Group₃.mul_inv, mul_one]
    _ = c := by simp only [mul_one]

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G



class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

-- Helper lemma for the next proof. Mathlib has `neg_eq_neg_one_mul` for
-- types α with [MulOneClass α] [HasDistribNeg α]
lemma neg_eq_neg_one_mul₃ {G : Type} [Ring₃ G] {a : G} : -a = -1 * a := by
  have : a + -1 * a = 0 := by
    calc
      a + -1 * a = 1 * a + -1 * a := by rw [one_mul]
      _          = (1 + -1) * a := by rw [Ring₃.right_distrib]
      _          = 0 * a := by rw [AddGroup₃.add_neg]
      _          = 0 := by rw [zero_mul]
  exact left_neg_eq_right_neg' (AddGroup₃.neg_add a) this

attribute [aesop norm] one_mul Ring₃.right_distrib AddGroup₃.add_neg
attribute [aesop unsafe 50%] zero_mul Ring₃.right_distrib

-- Same example `neg_eq_neg_one_mul` where most of the proof steps are found automatically by
-- aesop. Most are just applications of simp_all only [...]
set_option trace.aesop true
example {G : Type} [Ring₃ G] {a : G} : -a = -1 * a := by
  have : a + -1 * a = 0 := by
    calc
      a + -1 * a = 1 * a + -1 * a := by aesop
      _          = (1 + -1) * a := by rw [Ring₃.right_distrib]  -- can't get aesop working here
      _          = 0 * a := by aesop
      _          = 0 := by aesop
  aesop
  -- Proof script:
  -- apply left_neg_eq_right_neg'
  -- on_goal 2 => {exact this
  -- }
  -- · simp_all only [AddGroup₃.neg_add]


-- Prove that we can produce an additive commutative group from Ring₃,
-- which does not include an addition is commutative axiom. The key part is
-- the above lemma and left distributing multiplication by -1.
instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
    intro a b
    have hz : -(a + b) + (b + a) = 0 := by
      calc
        -(a + b) + (b + a) = -1*(a + b) + (b + a) := by rw [neg_eq_neg_one_mul₃]
        _ = (-1 * a + -1 * b) + (b + a) := by rw [Ring₃.left_distrib]
        _ = (-a + -b) + (b + a) := by repeat rw [← neg_eq_neg_one_mul₃]
        _ = -a + (-b + b) + a := by simp only [add_assoc₃]
        _ = -a + 0 + a := by rw [AddGroup₃.neg_add _]
        _ = -a + a := by rw [AddGroup₃.toAddMonoid₃.add_zero _]
        _ = 0 := AddGroup₃.neg_add _
    -- Note: aesop closes the goal at this point:
    -- aesop?

    -- rename_i inst
    -- aesop_unfold
    -- apply left_neg_eq_right_neg'
    -- on_goal 2 => exact hz
    -- simp_all only [AddGroup₃.add_neg]
    have hnab : -(a + b) + (a + b) = 0 := AddGroup₃.neg_add _
    have hz' : -(a + b) + (b + a) = -(a + b) + (a + b) := hnab ▸ hz
    exact (add_left_cancel₃ hz').symm
    }

instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

-- Note: matching parameter convensions so Nat order instance fields apply directly
class Preorder₁ (α : Type) extends LE₁ α where
  le_refl (a : α): a ≤₁ a
  le_trans {a b c : α} : a ≤₁ b → b ≤₁ c → a ≤₁ c

class PartialOrder₁ (α : Type) extends Preorder₁ α where
  le_antisymm {a b : α} (h1 : a ≤₁ b) (h2 : b ≤₁ a) : a = b

class OrderedCommMonoid₁ (α : Type) extends AddCommMonoid α, PartialOrder₁ α where
  le_of_mul_left (a b c : α) : a ≤₁ b → c + a ≤₁ c + b

-- Note: Nat has an AddCommMonoid instance, but not CommMonoid in Mathlib
instance : OrderedCommMonoid₁ ℕ where
  le := Nat.le
  le_refl := Nat.le_refl
  le_trans := Nat.le_trans
  le_antisymm := Nat.le_antisymm
  le_of_mul_left a b c := by
    intro h
    apply Nat.add_le_add_left
    assumption


/- Hierarchies with more than one data carrying class: Modules -/

class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul


/-- M is an R-module

  **Note**: `AddCommGroup₃ M` can't be listed as an extension on the right. Doing so
  leads Lean (through the `class` mechanism) to create a function `toAddCommGroup₃`
  on `M` that has ring, ring instance, and module types on the left of it's signature.
  However, the ring and ring instance are unconstrained on the right side, so finding
  such an instance amounts to choosing an arbitrary one from the instance database; almost
  surely not what we want. So the class mechanism forbids it.
-/
class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib

@[simp]
def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

@[simp]
lemma nsmul₁_zero {M : Type} [AddCommGroup₃ M] : ∀ (a: ℕ), nsmul₁ a (0: M) = (0: M) := by
  intro a
  induction a with
  | zero => unfold nsmul₁; rfl
  | succ j ih =>
    unfold nsmul₁
    simp only [ih, zero_add]

@[simp]
lemma nsmul₁_one {M : Type} [AddCommGroup₃ M] (m: M) : nsmul₁ 1 m = m := by
  simp only [nsmul₁, add_zero]

example {M: Type} [AddCommGroup₃ M] (n: ℕ) : (0: M) = nsmul₁ n 0 := by
  rw [nsmul₁_zero]

@[simp]
lemma add_nsmul₁ {M : Type} [AddCommGroup₃ M] :
    ∀ (a b : ℕ) (m : M), nsmul₁ (a + b) m = nsmul₁ a m + nsmul₁ b m := by
    intro a b m
    induction a with
    | zero => simp only [nsmul₁, zero_add, zero_add]
    | succ j ih =>
      simp only [nsmul₁]
      calc
        nsmul₁ (j + 1 + b) m = nsmul₁ (j + b + 1) m := by congr 1; omega
        _                    = m + nsmul₁ (j + b) m := by simp only [nsmul₁]
        _                    = m + nsmul₁ j m + nsmul₁ b m := by rw [ih, add_assoc₃]

lemma nsmul₁_add {M : Type} [AddCommGroup₃ M] :
    ∀ (a : ℕ) (m n: M), nsmul₁ a (m + n) = nsmul₁ a m + nsmul₁ a n := by
  intro a m n
  induction a with
  | zero => simp only [nsmul₁, zero_add]
  | succ b ih =>
    simp only [add_nsmul₁, nsmul₁_one, ih]
    -- ugh, cannot get this to work:
    -- simp only [add_assoc₃, AddCommGroup₃.add_comm]
    calc
      nsmul₁ b m + nsmul₁ b n + (m + n) = nsmul₁ b m + (nsmul₁ b n + (m + n)) := by rw [add_assoc₃]
      _                                 = nsmul₁ b m + ((nsmul₁ b n + m) + n) := by rw [add_assoc₃]
      _                                 = nsmul₁ b m + ((m + nsmul₁ b n) + n) := by rw [AddCommGroup₃.add_comm m _]
      _                                 = nsmul₁ b m + (m + (nsmul₁ b n + n)) := by rw [add_assoc₃]
      _                                 = nsmul₁ b m + m + (nsmul₁ b n + n) := by rw [add_assoc₃]

namespace AddGroup₃
lemma neg_of_add_eq_add_of_neg {M : Type} [AddCommGroup₃ M] :
    ∀ (a b: M), -(a + b) = -a + -b := by
  intro a b
  have h : (a + b) + (-a + -b) = 0 := by
    calc
      (a + b) + (-a + -b) = (a + b + -a) + -b := by rw [← add_assoc₃]
      _                   = (a + (b + -a)) + -b := by rw [← add_assoc₃]
      _                   = (a + (-a + b)) + -b := by rw [AddCommGroup₃.add_comm b (-a)]
      _                   = (a + -a + b) + -b := by rw [← add_assoc₃]
      _                   = (a + -a) + (b + -b) := by rw [← add_assoc₃]
      _                   = 0 := by
                                   repeat rw [add_neg]
                                   rw [zero_add]
  exact neg_eq_of_add h
end AddGroup₃

lemma nsmul₁_neg {M : Type} [AddCommGroup₃ M] :
    ∀ (a : ℕ) (m: M), nsmul₁ a (-m) = -nsmul₁ a m := by
  intro a m
  induction a with
  | zero =>
    simp only [nsmul₁]
    calc
      (0: M) = -0 + 0 := by rw [AddGroup₃.neg_add]
      _ = -0 := by rw [add_zero]
  | succ b ih =>
    simp only [nsmul₁, nsmul₁_add, ih]
    apply (AddGroup₃.neg_of_add_eq_add_of_neg m (nsmul₁ b m)).symm

@[simp]
lemma mul_nsmul₁ {M : Type} [AddCommGroup₃ M] :
    ∀ (a b : ℕ) (m : M), nsmul₁ (a * b) m = nsmul₁ a (nsmul₁ b m) := by
    intro a b m
    induction a with
    | zero => simp only [nsmul₁, Nat.zero_mul]
    | succ j ih =>
      simp only [nsmul₁, Nat.add_mul, Nat.one_mul, add_nsmul₁, ih, add_comm]

@[simp]
def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a

/-
"Proving every AddCommGroup naturally has the structure of a ℤ-module is
a bit tedious..."
-/
instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := by intro m; simp only [zsmul₁, nsmul₁]
    -- aesop  -- or aesop solves it
  one_smul := by intro m; simp only [zsmul₁, nsmul₁, add_zero]
  mul_smul := by
    intro a b m
    match a, b with
    | .ofNat j, .ofNat k =>
      -- TODO: don't know how to get simp to work with coe Nat -> Int
      rw [Int.ofNat_eq_coe, Int.ofNat_eq_coe, Int.ofNat_mul_ofNat]
      simp only [zsmul₁, Int.ofNat_mul, Int.ofNat_mul_ofNat, mul_nsmul₁]
    | Int.ofNat j, Int.negSucc k =>
      -- TODO: this case is very tedious
      simp only [zsmul₁, Int.ofNat_eq_coe, Int.ofNat_mul_negSucc']
      match j with
      | 0 =>
        rw [zero_mul]
        simp only [Int.negOfNat_eq, Int.ofNat_eq_coe, Int.neg_ofNat_zero, nsmul₁]
      | l + 1 =>
        have : (l + 1) * k.succ = l * k.succ + k + 1 := by
          rw [add_mul, Nat.succ_eq_add_one, one_mul]
          omega
        simp only [zsmul₁, Int.ofNat_eq_coe, Int.ofNat_mul_negSucc, Int.ofNat_mul,
                   this, Int.negOfNat, nsmul₁_add, nsmul₁_neg]
        congr 1
        simp only [Nat.succ_eq_add_one, nsmul₁_one, nsmul₁_add, mul_nsmul₁, add_assoc₃, mul_add]
        repeat rw [add_nsmul₁]
        simp only [mul_one, nsmul₁_one, nsmul₁_add, mul_nsmul₁, add_assoc₃]
    | Int.negSucc j, Int.ofNat k =>
      sorry
    | Int.negSucc j, Int.negSucc k => sorry
  add_smul := sorry
  smul_add := sorry

#synth Module₁ ℤ ℤ -- abGrpModule ℤ


class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
