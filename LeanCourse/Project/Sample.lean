/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

open Topology

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/

/- useful definitions and theorems: -/
#check instTopologicalSpaceSum
#check instTopologicalSpaceSubtype
#check instTopologicalSpaceQuotient
#check TopologicalSpace
#check Setoid

/- The adjunction space -/
/- Do I want this to be a class itself or rather an instance of the class TopologicalSpace? -/

def equivalence_of_images (X Y A : Type*) (f₁ : A → X) (f₂ : A → Y) {hf₁ : Injective f₁} {hf₂ : Injective f₂} : Setoid (X ⊕ Y) where
  r x y := sorry -- match x with
  --| match y with
  --  |
  --  |
  --| match y with
  --  |
  --  |
  --∃ a : A, f₁ a = x ∧ f₂ a = y
  iseqv := {
    refl := sorry
    symm := sorry
    trans := sorry
  }


/-
variable (X Y A : Type*)
variable (f₁ : A → X)
variable (f₂ : A → Y)

lemma injectivef₁ : Injective f₁ := by sorry
lemma injectivef₂ : Injective f₂ := by sorry

#check (equivalence_of_images X Y A f₁ f₂).r
-/


--def AdjunctionSpace (X Y A : Type*) (f₁ : A → X) (f₂ : A → Y) {hf₁ : Injective f₁} {hf₂ : Injective f₂} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] := {
--  @Quotient (X ⊕ Y) (equivalence_of_images X Y A f₁ f₂)
--}
