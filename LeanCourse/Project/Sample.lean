/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

open Topology

open TopologicalSpace

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/

/- useful definitions and theorems: -/
#check instTopologicalSpaceSum
#check instTopologicalSpaceSubtype
#check instTopologicalSpaceQuotient
#check TopologicalSpace
#check Setoid
#check Sum.inr.injEq
#check Sum.inl.injEq

/-- We define an equivalence relation on the disjoint union of two types X and Y
with respect to a type A and two injective functions f₁ : A → X and f₂ : A → Y:
The equivalence relation is the induced equivalence relation of {incl_X f₁ a ∼ incl_Y f₂ a},
where incl_X and incl_Y are the canonical inclusion maps.  -/
def equivalence_of_images {X Y A : Type*} {f₁ : A → X} {f₂ : A → Y}
(hf₁ : Injective f₁) (hf₂ : Injective f₂) : Setoid (X ⊕ Y) where
  r x y := (x = y) ∨ (∃ a : A, Sum.inl (f₁ a) = x ∧ Sum.inr (f₂ a) = y)
  ∨ (∃ a : A, Sum.inl (f₁ a) = y ∧ Sum.inr (f₂ a) = x)
  iseqv := {
    refl := by simp
    symm := by simp
    trans := by {
      intro x y z hx hy
      obtain h₁ | h₂ | h₃ := hx
      · obtain h₄ | h₅ | h₆ := hy
        · rw [h₄] at h₁
          left
          exact h₁
        · obtain ⟨ a, ha ⟩ := h₅
          rw [← h₁] at ha
          right
          left
          use a
        · obtain ⟨ a, ha ⟩ := h₆
          rw [← h₁] at ha
          right
          right
          use a
      · obtain h₄ | h₅ | h₆ := hy
        · obtain ⟨ a, ha ⟩ := h₂
          rw [h₄] at ha
          right
          left
          use a
        · obtain ⟨ a₁, ha₁⟩ := h₂
          obtain ⟨ a₂, ha₂⟩ := h₅
          obtain ⟨ ha₁1, ha₁2⟩ := ha₁
          obtain ⟨ ha₂1, ha₂2⟩ := ha₂
          rw [← ha₂1] at ha₁2
          contradiction
        · obtain ⟨a₁, ha₁⟩ := h₂
          obtain ⟨a₂, ha₂⟩ := h₆
          obtain ⟨ha₁1, ha₁2⟩ := ha₁
          obtain ⟨ha₂1, ha₂2⟩ := ha₂
          rw [← ha₂2] at ha₁2
          have h₇ : f₂ a₁ = f₂ a₂ := by aesop
          apply hf₂ at h₇
          rw [h₇] at ha₁1
          rw [ha₁1] at ha₂1
          left
          exact ha₂1
      · obtain h₄ | h₅ | h₆ := hy
        · obtain ⟨ a, ha⟩ := h₃
          rw [h₄] at ha
          right
          right
          use a
        · obtain ⟨a₁, ha₁⟩ := h₃
          obtain ⟨a₂, ha₂⟩ := h₅
          obtain ⟨ha₁1, ha₁2⟩ := ha₁
          obtain ⟨ha₂1, ha₂2⟩ := ha₂
          rw [← ha₂1] at ha₁1
          have h₇ : f₁ a₁ = f₁ a₂ := by aesop
          apply hf₁ at h₇
          rw [h₇] at ha₁2
          rw [ha₁2] at ha₂2
          left
          exact ha₂2
        · obtain ⟨a₁, ha₁⟩ := h₃
          obtain ⟨a₂, ha₂⟩ := h₆
          obtain ⟨ha₁1, ha₁2⟩ := ha₁
          obtain ⟨ha₂1, ha₂2⟩ := ha₂
          rw [← ha₂2] at ha₁1
          contradiction
    }
  }

/-- We define the adjunction space (as a set) as the quotient of X ⊕ Y with respect to the equivalence relation equivalence_of_images. -/
def AdjunctionSpace {X Y A: Type*} {f₁ : A → X} {f₂ : A → Y}
(hf₁ : Injective f₁) (hf₂ : Injective f₂)
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] :=
    Quotient (equivalence_of_images hf₁ hf₂)

/-- The adjunction space of a topological space is the induced instance of TopologicalSpace on AdjunctionSpace. -/
instance instTopologicalSpaceAdjunction {X Y A: Type*} {f₁ : A → X} {f₂ : A → Y}
(hf₁ : Injective f₁) (hf₂ : Injective f₂)
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] :
    TopologicalSpace (AdjunctionSpace hf₁ hf₂) := by {
      unfold AdjunctionSpace
      infer_instance
    }

--@[simp]
--lemma universalPropertyAdjunctionSpace {X Y Z A : Type*} {f₁ : A → X} {f₂ : A → Y}
--(g₁ : X → Z) (g₂ : Y → Z) (hf₁ : Injective f₁) (hf₂ : Injective f₂)
--[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace A] :
--∃! h : AdjunctionSpace hf₁ hf₂ → Z,
