import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import MilSolutions.Common

@[ext]
structure GaussInt where
  re : ℤ
  im : ℤ

namespace GaussInt

instance : Zero GaussInt :=
  ⟨⟨0, 0⟩⟩

instance : One GaussInt :=
  ⟨⟨1, 0⟩⟩

instance : Add GaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg GaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

-- (x.re + i * x.im) * (y.re + i * y.im)
instance : Mul GaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

theorem zero_def : (0 : GaussInt) = ⟨0, 0⟩ :=
  rfl

theorem one_def : (1 : GaussInt) = ⟨1, 0⟩ :=
  rfl

theorem add_def (x y : GaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

theorem neg_def (x : GaussInt) : -x = ⟨-x.re, -x.im⟩ :=
  rfl

theorem mul_def (x y : GaussInt) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl

@[simp]
theorem zero_re : (0 : GaussInt).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem one_re : (1 : GaussInt).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : GaussInt) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : GaussInt) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl

-- auto-expansion of the structure's fields can be done here using the lightbulb
-- instance myInstCommRing : CommRing GuassInt := _

instance instCommRing : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  neg_add_cancel := by
    intro
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring
  mul_assoc := by
    intros
    ext <;> simp <;> ring
  one_mul := by
    intro
    ext <;> simp
  mul_one := by
    intro
    ext <;> simp
  left_distrib := by
    intros
    ext <;> simp <;> ring
  right_distrib := by
    intros
    ext <;> simp <;> ring
  mul_comm := by
    intros
    ext <;> simp <;> ring
  zero_mul := by
    intros
    ext <;> simp
  mul_zero := by
    intros
    ext <;> simp

@[simp]
theorem sub_re (x y : GaussInt) : (x - y).re = x.re - y.re :=
  rfl

@[simp]
theorem sub_im (x y : GaussInt) : (x - y).im = x.im - y.im :=
  rfl

-- structures that have two distinct elements
instance : Nontrivial GaussInt := by
  use 0, 1
  rw [Ne, GaussInt.ext_iff]
  simp

end GaussInt

example (a b : ℤ) : a = b * (a / b) + a % b :=
  Eq.symm (Int.ediv_add_emod a b)

example (a b : ℤ) : b ≠ 0 → 0 ≤ a % b :=
  Int.emod_nonneg a

example (a b : ℤ) : b ≠ 0 → a % b < |b| :=
  Int.emod_lt a

namespace Int

def div' (a b : ℤ) :=
  (a + b / 2) / b

def mod' (a b : ℤ) :=
  (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a := by
  rw [div', mod']
  linarith [Int.ediv_add_emod (a + b / 2) b]

theorem abs_mod'_le (a b : ℤ) (h : 0 < b) : |mod' a b| ≤ b / 2 := by
  rw [mod', abs_le]
  constructor
  · linarith [Int.emod_nonneg (a + b / 2) h.ne']
  have := Int.emod_lt_of_pos (a + b / 2) h
  have := Int.ediv_add_emod b 2
  have := Int.emod_lt_of_pos b zero_lt_two
  linarith

theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]

end Int

-- Lemmas:

/- Addition is monotone in an ordered additive commutative group. -/
-- add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

/- In a strict ordered ring, `0 ≤ 1`. -/
-- zero_le_one : 0 ≤ (1 : α)

/- The product of two positive elements is positive. -/
-- mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b

/- LinearOrder trichotemy -/
-- x < y ∨ x = y ∨ y < x

-- Sketch:
-- by_contra gets us case 1: x != 0
--   by sq_pos_iff -> 0 < x^2
--   y^2 < x^2 + y^2 = 0
--   y^2 < 0
--   by sq_pos_iff and contradiction, y = 0
-- etc...
theorem sq_add_sq_eq_zero {α : Type*} [LinearOrderedRing α] (x y : α) :
    x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  . intro h
    by_contra dj
    push_neg at dj
    by_cases hxz : x = 0
    · have : y ≠ 0 := dj hxz
      rw [hxz, sq, zero_mul, zero_add] at h
      exact this (sq_eq_zero_iff.mp h)

    · -- case: x ≠ 0: use linear order to show that y = 0
      have : 0 < x^2 := sq_pos_iff.mpr hxz
      have y2lt : y^2 < 0 := by
        calc y^2
          _ = y^2 + 0 := by rw [add_zero]
          _ < y^2 + x^2 := by apply add_lt_add_left this (y^2)
          _ = 0 := by rw [add_comm]; exact h

      -- y^2 < 0 → y = 0 is probably a lemma
      have : y = 0 := by
        by_contra hz
        have : 0 < y^2 := sq_pos_iff.mpr hz
        have : y^2 < y^2 := y2lt.trans this
        exact (lt_self_iff_false (y^2)).mp this

      rw [this] at y2lt
      rw [sq, zero_mul] at y2lt
      exact (lt_self_iff_false 0).mp y2lt
  · rintro ⟨xz, yz⟩
    rw [xz, yz, sq, zero_mul, zero_add]

namespace GaussInt

def norm (x : GaussInt) :=
  x.re ^ 2 + x.im ^ 2

@[simp]
theorem norm_nonneg (x : GaussInt) : 0 ≤ norm x := by
  rw [norm]
  linarith [sq_nonneg x.re, sq_nonneg x.im]

theorem norm_eq_zero (x : GaussInt) : norm x = 0 ↔ x = 0 := by
  rw [norm]
  constructor
  · intro h
    let ⟨ hre, him ⟩ := (sq_add_sq_eq_zero x.re x.im).mp h
    apply x.ext <;> assumption
  intro h
  apply (sq_add_sq_eq_zero x.re x.im).mpr
  constructor
  · convert zero_re
  convert zero_im

theorem norm_pos (x : GaussInt) : 0 < norm x ↔ x ≠ 0 := by
  constructor
  · intro h
    by_contra ch
    rw [norm] at h
    have xr : x.re = 0 := by rw [ch]; apply zero_re
    have xi : x.im = 0 := by rw [ch]; apply zero_im
    rw [xr, xi] at h
    contradiction

  intro (h : x ≠ 0)
  show 0 < norm x
  rw [norm]
  by_cases hr : x.re ≠ 0
  · have hr : 0 < x.re^2 := sq_pos_iff.mpr hr
    have hi : 0 ≤ x.im^2 := sq_nonneg x.im
    exact Int.add_pos_of_pos_of_nonneg hr hi
  have hr : x.re = 0 := by tauto
  rw [hr, zero_pow (by norm_num), zero_add]

  suffices hi : x.im ≠ 0
  · exact (sq_pos_iff.mpr hi)
  intro hi
  have : x = 0 := by
    apply x.ext
    · rw [hr, zero_re]
    · rw [hi, zero_im]
  exact h this

theorem norm_mul (x y : GaussInt) : norm (x * y) = norm x * norm y := by
  rw [mul_def, norm, norm, norm]
  simp only
  ring

def conj (x : GaussInt) : GaussInt :=
  ⟨x.re, -x.im⟩

@[simp]
theorem conj_re (x : GaussInt) : (conj x).re = x.re :=
  rfl

@[simp]
theorem conj_im (x : GaussInt) : (conj x).im = -x.im :=
  rfl

theorem norm_conj (x : GaussInt) : norm (conj x) = norm x := by simp [norm]

instance : Div GaussInt :=
  ⟨fun x y ↦ ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩⟩

instance : Mod GaussInt :=
  ⟨fun x y ↦ x - y * (x / y)⟩

theorem div_def (x y : GaussInt) :
    x / y = ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩ :=
  rfl

theorem mod_def (x y : GaussInt) : x % y = x - y * (x / y) :=
  rfl

theorem norm_mod_lt (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have norm_y_pos : 0 < norm y := by rwa [norm_pos]
  have H1 : x % y * conj y = ⟨Int.mod' (x * conj y).re (norm y), Int.mod' (x * conj y).im (norm y)⟩
  · ext <;> simp [Int.mod'_eq, mod_def, div_def, norm] <;> ring
  have H2 : norm (x % y) * norm y ≤ norm y / 2 * norm y
  · calc
      norm (x % y) * norm y = norm (x % y * conj y) := by simp only [norm_mul, norm_conj]
      _ = |Int.mod' (x.re * y.re + x.im * y.im) (norm y)| ^ 2
          + |Int.mod' (-(x.re * y.im) + x.im * y.re) (norm y)| ^ 2 := by simp [H1, norm, sq_abs]
      _ ≤ (y.norm / 2) ^ 2 + (y.norm / 2) ^ 2 := by gcongr <;> apply Int.abs_mod'_le _ _ norm_y_pos
      _ = norm y / 2 * (norm y / 2 * 2) := by ring
      _ ≤ norm y / 2 * norm y := by gcongr; apply Int.ediv_mul_le; norm_num
  calc norm (x % y) ≤ norm y / 2 := le_of_mul_le_mul_right H2 norm_y_pos
    _ < norm y := by
        apply Int.ediv_lt_of_lt_mul
        · norm_num
        · linarith

theorem coe_natAbs_norm (x : GaussInt) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)

theorem natAbs_norm_mod_lt (x y : GaussInt) (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  apply Int.ofNat_lt.1
  simp only [Int.natCast_natAbs, abs_of_nonneg, norm_nonneg]
  apply norm_mod_lt x hy

theorem not_norm_mul_left_lt_norm (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    ¬(norm (x * y)).natAbs < (norm x).natAbs := by
  apply not_lt_of_ge
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  apply Int.ofNat_le.1
  rw [coe_natAbs_norm]
  exact Int.add_one_le_of_lt ((norm_pos _).mpr hy)

instance : EuclideanDomain GaussInt :=
  { GaussInt.instCommRing with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_mul_add_remainder_eq :=
      fun x y ↦ by
        simp only
        rw [mod_def, add_comm]
        ring
    quotient_zero := fun x ↦ by
      simp only [div_def, norm, Int.div']
      rw [zero_re, zero_im]
      -- TODO: fix this seemingly unneccessary simplification. The orig was
      -- simply `rfl`
      simp only [mul_re, conj_re, zero_re, mul_zero, conj_im, zero_im, neg_zero, sub_self, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, EuclideanDomain.zero_div,
        EuclideanDomain.div_zero, mul_im]
      rfl
    r := (measure (Int.natAbs ∘ norm)).1
    r_wellFounded := (measure (Int.natAbs ∘ norm)).2
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := not_norm_mul_left_lt_norm }

example (x : GaussInt) : Irreducible x ↔ Prime x :=
  irreducible_iff_prime

end GaussInt