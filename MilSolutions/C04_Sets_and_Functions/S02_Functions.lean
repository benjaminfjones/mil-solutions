import MilSolutions.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  -- simp only [preimage_inter, mem_inter_iff, mem_preimage]
  rfl

#check f '' s  -- : Set β

-- Note: The rintro decompositons don't actually need to rewrite `f x = y` using `rfl`
-- because of definitional equality
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · -- y ∈ f '' (s ∪ t) defined as
    -- ∃ x, x ∈ s ∪ t ∧ f x = y
    rintro ⟨x, xs | xt, _ /- rfl -/⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, _ /- rfl -/⟩ | ⟨x, xt, _ /- rfl -/⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  -- use x, xs  -- Done
  -- illustrates how `use` follows up with `rfl` when it can close the goal
  refine ⟨ x, xs, ?_ ⟩
  rfl

-- AKA: `image_subset_iff`
--
-- `image f` and  `preimage f` are an instance of a Galois connection between Set α and Set β,
-- each partially ordered by the subset relation.
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro fsv
    -- fsv : { y | ∃ x ∈ s, f x = y } → v
    intro x xs
    have h : f x ∈ f '' s := by
      refine ⟨ x, xs, ?_ ⟩
      rfl
    have h' : f x ∈ v := fsv h
    assumption
  intro ssv  -- s → f ⁻¹' v
  -- goal: exhibit a fn from f '' s → v
  intro z zfs
  rcases zfs with ⟨w, hw, rfl⟩
  exact ssv hw


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x xffs
  have hfx : f x ∈ f '' s := xffs  -- restate the defintion
  rcases hfx with ⟨y, hy, fxfy⟩
  rw [← h fxfy]
  assumption

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨z, hz, rfl⟩
  -- ⊢ f z ∈ u  def=  z ∈ f ⁻¹' u
  assumption


example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, hx⟩
  have hxu : f x ∈ u := by rw [hx]; assumption
  refine ⟨ x, hxu, ?_⟩
  assumption


example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y hy
  rcases hy with ⟨ x, xs, fxy⟩
  have : x ∈ t := h xs
  use x


example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
  -- { x | ∃ y ∈ u ∧ f x = y } → { x | ∃ y ∈ v ∧ f x = y }
  fun _x xfu => h xfu

-- AKA: `preimage_union`
example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · rintro (hu | hv)
    · left; assumption
    right; assumption
  rintro (xfu | xfv)
  · left; assumption
  right; assumption


example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, fxy⟩
  constructor
  rw [← fxy]
  use x
  use x


example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨yfs, yft⟩
  rcases yfs with ⟨x, xs, fxy⟩  -- an `x` mapping to `y` in `f '' s`
  use x
  -- could use refine ⟨?_, fxy⟩, but we can emphasize the remaining goal with suffices
  suffices xst : x ∈ s ∩ t by exact ⟨xst, fxy⟩
  rcases yft with ⟨x', xt, fxy'⟩
  rw [← fxy] at fxy'
  have xx' : x' = x := h fxy'
  rw [xx'] at xt
  exact ⟨xs, xt⟩


example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  · rintro ⟨x, xs, fxy⟩
    rw [mem_iUnion] at *
    rcases xs with ⟨j, xAj⟩
    use j
    have him : f x ∈ f '' (A j) := by exact mem_image_of_mem f xAj
    rwa [fxy] at him
  rw [mem_iUnion]
  rintro ⟨j, x, xAj, fxy⟩
  have hxUAi : x ∈ ⋃ i, A i := by rw [mem_iUnion]; use j
  rw [← fxy]
  exact mem_image_of_mem f hxUAi


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro y ⟨x, xAj, fxy⟩
  rw [mem_iInter] at *
  intro i
  rw [← fxy]
  exact mem_image_of_mem f (xAj i)


-- Note: original does not have a typo extra hypothesis: `(i : I)`, it is required
-- unless we resort to the axiom of choice for `I`.
example (i₀ : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rw [subset_def]
  intro x
  rw [mem_iInter]
  intro hx
  rcases hx i₀ with ⟨z, _, fzx⟩
  refine ⟨z, ?_, fzx⟩

  show z ∈ ⋂ i, A i
  rw [mem_iInter]
  intro j
  rcases hx j with ⟨zj, zjAj, fzjx⟩
  have zzj : z = zj := injf (Eq.trans fzx fzjx.symm)
  rwa [← zzj] at zjAj


example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp only [mem_preimage, mem_iUnion]


example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp only [mem_preimage, mem_iInter]


example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
