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
  intro a ha
  simp_all only [mem_diff, mem_image, not_exists, not_and]
  obtain ⟨⟨w, ⟨ws, fwa⟩⟩, aright⟩ := ha
  subst fwa
  use w
  simp_all only [true_and, and_true]
  intro hwt
  have : ¬ f w = f w := aright w hwt
  contradiction


-- AKA: `preimage_diff`
example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  simp_all only [preimage_diff, subset_refl]

-- aesop proves this in 24 lines
-- we have 12 lines
example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  simp_all only [mem_inter_iff, mem_image, mem_preimage]
  constructor
  · rintro ⟨⟨x1, x1s, fx1x⟩, xv⟩
    use x1
    refine ⟨⟨x1s, ?_⟩, fx1x⟩
    rwa [fx1x]
  · rintro ⟨x1, ⟨x1s, fx1v⟩, fx1x⟩
    rw [← fx1x] at *
    constructor
    · use x1
    assumption


example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  -- convert to preimage, which ends up not depending on `u` at all
  simp_all only [subset_inter_iff, image_subset_iff, inter_subset_right, and_true]
  have : s ∩ f ⁻¹' u ⊆ s := by apply inter_subset_left
  apply subset_trans this
  exact subset_preimage_image f s


example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  simp only [preimage_inter, subset_inter_iff, inter_subset_right, and_true]
  -- same exact proof as above after the simp
  have : s ∩ f ⁻¹' u ⊆ s := by apply inter_subset_left
  apply subset_trans this
  exact subset_preimage_image f s


example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  simp only [preimage_union, union_subset_iff, subset_union_right, and_true]
  apply subset_trans (subset_preimage_image f s)
  exact subset_union_left

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
  intro x1 x1nn x2 x2nn h
  calc
    x1 = (√x1)^2 := by apply (sq_sqrt x1nn).symm
    _  = (√x2)^2 := by rw [h]
    _  = x2      := by apply sq_sqrt x2nn

-- same proof
example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x1 x1nn x2 x2nn h
  have h' : x1^2 = x2^2 := by assumption  -- restate h
  calc
    x1 = √(x1^2) := by apply (sqrt_sq x1nn).symm
    _  = √(x2^2) := by rw [h']
    _  = x2      := by apply sqrt_sq x2nn

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext z
  constructor
  · rintro ⟨x, _, sqrt_xz⟩
    have sqrt_x_nn : 0 ≤ √x := by apply sqrt_nonneg
    rwa [sqrt_xz] at sqrt_x_nn
  intro znn
  use z^2
  constructor
  · show 0 ≤ z^2
    apply sq_nonneg
  exact sqrt_sq znn

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext z
  constructor
  · rintro ⟨x, fxz⟩
    have h : x^2 = z := fxz  -- restate fxz
    rw [← h]
    show 0 ≤ x^2  -- restate goal; didn't think this would be neccesary
    apply sq_nonneg
  intro h
  use √z
  exact sq_sqrt h

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

#print LeftInverse
#print RightInverse

-- TODO: could be shorter, oneline?
example : Injective f ↔ LeftInverse (inverse f) f := by
  -- ∀ x1 x2, f x1 = f x2 → x1 = x2  ↔  ∀ x, (inverse f) (f x) = x
  constructor
  · intro finj x
    have hinv : ∃z, f z = f x := by use x
    rw [inverse, dif_pos hinv]
    exact finj (Classical.choose_spec hinv)
  intro hli x1 x2 he
  have hli2 : (inverse f) (f x2) = x2 := hli x2
  exact (hli x1).symm.trans (he ▸ hli2)


-- Pow, short proof! 💥
--
-- Using _'s to identify types, then unifying with things that can be constructed
-- easily from context
--
-- aesop? and simp? get nowhere
example : Injective f ↔ LeftInverse (inverse f) f :=
  -- ∀ x1 x2, f x1 = f x2 → x1 = x2  ↔  ∀ x, (inverse f) (f x) = x
  ⟨ fun finj => fun x => finj (inverse_spec (f x) (by use x)),
    fun linv => fun x1 x2 fx1x2 => (linv x1).symm.trans (fx1x2.symm ▸ (linv x2))
    -- more fully spelling out the motive in the substitution:
    -- fun linv => fun x1 x2 fx1x2 => Eq.trans (linv x1).symm (Eq.subst (motive := fun z => (inverse f) z = x2) fx1x2.symm (linv x2))
  ⟩


-- Pow, short proof! 💥
example : Surjective f ↔ RightInverse (inverse f) f :=
  -- ∀ y, ∃ x, f x = y  ↔  ∀ y, f ((inverse f) y) = y
  ⟨ fun fsurj => fun y => inverse_spec y (fsurj y),
    fun rinv  => fun y => ⟨(inverse f) y, rinv y⟩⟩

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
