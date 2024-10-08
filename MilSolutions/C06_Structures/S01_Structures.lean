import MilSolutions.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

namespace C06S01
noncomputable section

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption

def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

namespace Point

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl

def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- the same proof still works, but the goal view here is harder to read
  ext <;> dsimp
  repeat' apply add_comm

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  repeat' rw [add]
  ext <;> dsimp
  repeat' rw [add_assoc]

def smul (r : ℝ) (a : Point) : Point :=
  Point.mk (r * a.x) (r * a.y) (r * a.z)

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
  -- repeat' rw [add]
  -- repeat' rw [smul]
  simp only [add, smul]
  ext <;> dsimp
  repeat' rw [mul_add]

end Point

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

theorem interpolate_nonneg {a b lam: ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b)
    (lam_nonneg : 0 ≤ lam) (lam_le : lam ≤ 1) : 0 ≤ lam * a + (1 - lam) * b := by
  have : 0 ≤ 1 - lam := sub_nonneg.mpr lam_le
  apply add_nonneg
  · apply mul_nonneg lam_nonneg ha
  · apply mul_nonneg this hb

namespace StandardTwoSimplex

def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

noncomputable section

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

def weightedAverage (lam : Real) (lam_nonneg : 0 ≤ lam) (lam_le : lam ≤ 1)
    (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := lam * a.x + (1 - lam) * b.x
  y := lam * a.y + (1 - lam) * b.y
  z := lam * a.z + (1 - lam) * b.z
  x_nonneg := interpolate_nonneg a.x_nonneg b.x_nonneg lam_nonneg lam_le
  y_nonneg := interpolate_nonneg a.y_nonneg b.y_nonneg lam_nonneg lam_le
  z_nonneg := interpolate_nonneg a.z_nonneg b.z_nonneg lam_nonneg lam_le
  sum_eq := by
    calc
      lam * a.x + (1 - lam) * b.x +
      (lam * a.y + (1 - lam) * b.y) +
      (lam * a.z + (1 - lam) * b.z) = lam * (a.x + a.y + a.z) + (1-lam)*(b.x + b.y + b.z) := by ring
      _ = lam + (1 - lam) := by rw [a.sum_eq, b.sum_eq]; ring
      _ = 1 := by simp only [add_sub_cancel]

end

end StandardTwoSimplex

open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

-- set_option diagnostics true
def weightedAverage {n : Nat} (lam : Real) (lam_nonneg : 0 ≤ lam) (lam_le : lam ≤ 1)
    (a b : StandardSimplex n) : StandardSimplex n where
  V i := lam * a.V i + (1 - lam) * b.V i
  NonNeg := fun i => interpolate_nonneg (a.NonNeg i) (b.NonNeg i) lam_nonneg lam_le
  sum_eq_one := by
    calc (∑ i, (fun x => lam * a.V x + (1 - lam) * b.V x) i)
      _ = (∑ i, (fun x => lam * a.V x) i) + (∑ i, (fun x => (1 - lam) * b.V x) i) := by apply Finset.sum_add_distrib
      _ = lam * (∑ i, (fun x => a.V x) i) + (1 - lam) * (∑ i, (fun x => b.V x) i) := by repeat' rw [Finset.mul_sum]
      _ = lam + (1 - lam) := by
        rw [a.sum_eq_one, b.sum_eq_one, mul_one, mul_one]
      _ = 1 := by ring

end StandardSimplex

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end

def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x

def PReal :=
  { y : ℝ // 0 < y }

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end

def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def StandardSimplex' (n : ℕ) :=
  { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }

def StdSimplex := Σ n : ℕ, StandardSimplex n

section
variable (s : StdSimplex)

#check s.fst
#check s.snd

#check s.1
#check s.2

end
