import MIL.Common
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
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    simp
    specialize h ⟨x, xs, rfl⟩
    exact h
  · intro h y ys
    simp at ys
    rcases ys with ⟨x, xs, fxeq⟩
    rw [← fxeq]
    apply h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fxeq⟩
  apply h at fxeq
  rw [← fxeq]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, xs, rfl⟩
  simp at xs
  exact xs

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y hy
  simp
  rcases h y with ⟨x, fxeq⟩
  use x
  rw [fxeq]
  constructor; assumption; rfl

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, rfl⟩
  simp
  use x, h xs

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x; simp; intro hx
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x; rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  simp; constructor;
  · use x, xs
  · use x, xt

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y; rintro ⟨⟨x, xs, rfl⟩, ⟨x', xt, fxeq'⟩⟩
  simp; use x; constructor
  · constructor
    · exact xs
    · apply h at fxeq'; rw [← fxeq']; exact xt
  · rfl

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, h⟩; use x; constructor
  · constructor
    · exact xs
    · intro hxt; apply h; use x
  · rfl

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ; simp

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩; simp; use x
  · rintro ⟨x, ⟨xs, xv⟩, rfl⟩; simp; constructor
    · use x
    · exact xv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fxu⟩, rfl⟩;
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩; exact ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left; use x;
  · right; apply fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp; constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x;
  · rintro ⟨i, x, xAi, fxeq⟩
    use x; constructor
    · use i
    · exact fxeq


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro y; simp
  intro x h fxeq i
  use x; exact ⟨h i, fxeq⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro y; simp
  intro h
  rcases (h i) with ⟨x, xAi, fxeq⟩
  use x; constructor
  · intro i'
    rcases (h i') with ⟨x', xAi', fxeq'⟩
    rw [← fxeq] at fxeq'
    apply injf at fxeq'
    rw [← fxeq']; exact xAi'
  · exact fxeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x; simp;

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x; simp

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
  intro x hx y hy hxy
  calc
    x = sqrt x ^ 2 := by rw [sq_sqrt hx]
    _ = sqrt y ^ 2 := by rw [hxy]
    _ = y := by rw [sq_sqrt hy]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x hx y hy hxy
  dsimp at *
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq hx]
    _ = sqrt (y ^ 2) := by rw [hxy]
    _ = y := by rw [sqrt_sq hy]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · simp; intro x hx hxy; rw [← hxy];
    apply sqrt_nonneg
  · simp; intro hy;
    use (y ^ 2); constructor
    · apply pow_nonneg hy
    · apply sqrt_sq; assumption

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  · simp; intro x hxy; rw [← hxy]; apply pow_two_nonneg
  · simp; intro hy; use sqrt y; rw [sq_sqrt hy]

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

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro hf x
    apply hf
    apply inverse_spec
    use x
  · intro hf x1 x2 heq
    rw [← hf x1, ← hf x2, heq]


example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro hf y
    apply inverse_spec
    apply hf
  · intro hf y
    use (inverse f y)
    apply hf

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
  have h₂ : j ∈ S := by apply h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

-- COMMENTS: TODO: improve this
end
