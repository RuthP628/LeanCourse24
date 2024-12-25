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
#check instTopologicalSpaceQuotient
#check Sum.inr.injEq
#check Sum.inl.injEq
#check Sum.inl
#check Sum.inr
#check ContinuousMap
#check quotientMap_quotient_mk'
#check continuous_quotient_mk'
#check isOpenMap_inl
#check IsOpenMap
#check Quotient.mk'
#check Quotient
#check Setoid
#check Quotient.lift
#check continuous_quot_lift


/-- We define an equivalence relation on the disjoint union of two types X and Y
with respect to a type A and two injective functions f₁ : A → X and f₂ : A → Y:
The equivalence relation is the induced equivalence relation of {incl_X f₁ a ∼ incl_Y f₂ a},
where incl_X and incl_Y are the canonical inclusion maps.  -/
@[simp]
def equivalence_of_images {X Y A : Type*}{f₁ : A → X}{f₂ : A → Y}
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
def AdjunctionSpace {X Y A: Type*} {f₂ : A → Y}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
{f₁ : ContinuousMap A X} {f₂ : ContinuousMap A Y}
(hf₁ : Injective f₁) (hf₂ : Injective f₂) :=
    Quotient (equivalence_of_images hf₁ hf₂)

/-- The adjunction space of a topological space is the induced instance of TopologicalSpace on AdjunctionSpace. -/
instance instTopologicalSpaceAdjunction {X Y A: Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
{f₁ : ContinuousMap A X} {f₂ : ContinuousMap A Y}
(hf₁ : Injective f₁) (hf₂ : Injective f₂) :
    TopologicalSpace (AdjunctionSpace (f₁ := f₁) (f₂ := f₂) hf₁ hf₂) := by {
      unfold AdjunctionSpace
      infer_instance
    }

--lemma adjunction_symm {X Y A: Type*}
--[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
--(hf₁ : Injective f₁) (hf₂ : Injective f₂) :
--  AdjunctionSpace hf₁ hf₂ = AdjunctionSpace hf₂ hf₁

@[simp]
def pushout_map_1 {X Y A: Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
{f₁ : ContinuousMap A X} {f₂ : ContinuousMap A Y}
(hf₁ : Injective f₁) (hf₂ : Injective f₂) :
ContinuousMap X (AdjunctionSpace (f₁ := f₁) (f₂ := f₂) hf₁ hf₂) where
  toFun := fun x ↦ Quotient.mk' (s := equivalence_of_images hf₁ hf₂) (Sum.inl x)
  continuous_toFun := by {
    let canon_inj : X → X ⊕ Y := fun x ↦ Sum.inl x
    have h₁ : Continuous canon_inj := by exact continuous_inl
    let quotmap : X ⊕ Y → Quotient (equivalence_of_images hf₁ hf₂) := fun x ↦ Quotient.mk' (s := equivalence_of_images hf₁ hf₂) x
    have h₂ : Continuous quotmap := by exact continuous_quotient_mk'
    exact Continuous.comp' h₂ h₁
  }

@[simp]
def pushout_map_2 {X Y A: Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
{f₁ : ContinuousMap A X} {f₂ : ContinuousMap A Y}
(hf₁ : Injective f₁) (hf₂ : Injective f₂) :
ContinuousMap Y (AdjunctionSpace (f₁ := f₁) (f₂ := f₂) hf₁ hf₂) where
  toFun := fun y ↦ Quotient.mk' (s := equivalence_of_images hf₁ hf₂) (Sum.inr y)
  continuous_toFun := by {
    let canon_inj : Y → X ⊕ Y := fun y ↦ Sum.inr y
    have h₁ : Continuous canon_inj := by exact continuous_inr
    let quotmap : X ⊕ Y → Quotient (equivalence_of_images hf₁ hf₂) := fun x ↦ Quotient.mk' (s := equivalence_of_images hf₁ hf₂) x
    have h₂ : Continuous quotmap := by exact continuous_quotient_mk'
    exact Continuous.comp' h₂ h₁
  }

/-- The disjoint union is the coproduct in the category of topological spaces. -/
lemma univ_prop_coprod {X Y Z : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
(g₁ : ContinuousMap X Z)(g₂ : ContinuousMap Y Z) :
∃! h : ContinuousMap (X ⊕ Y) Z, g₁ = h ∘ Sum.inl ∧ g₂ = h ∘ Sum.inr := by {
  let h' : (X ⊕ Y) → Z
    | Sum.inl x => g₁ x
    | Sum.inr y => g₂ y
  let h'' : ContinuousMap (X ⊕ Y) Z := {
    toFun := h'
    continuous_toFun := {
      isOpen_preimage := by {
        intro s hs
        have h₁ : IsOpen (preimage g₁ s) := by {
          have h_1 : Continuous g₁ := by exact ContinuousMap.continuous g₁
          exact h_1.isOpen_preimage s hs
        }
        have h₂ : IsOpen (preimage g₂ s) := by {
          have h_1 : Continuous g₂ := by exact ContinuousMap.continuous g₂
          exact h_1.isOpen_preimage s hs
        }
        have h₃ : preimage h' s = {Sum.inl x | x ∈ preimage g₁ s} ∪ {Sum.inr y | y ∈ preimage g₂ s} := by {
          ext x
          constructor
          · intro hx
            simp
            match x with
            | Sum.inl x' => {
              left
              use x'
              constructor
              · exact hx
              · rfl
            }
            | Sum.inr y' => {
              right
              use y'
              constructor
              · exact hx
              · rfl
            }
          · intro hx
            obtain hx₁ | hx₂ := hx
            · simp at hx₁
              obtain ⟨ x', hx₁', hx₂' ⟩ := hx₁
              unfold preimage
              simp
              rw [← hx₂']
              unfold h'
              simp
              exact hx₁'
            · simp at hx₂
              obtain ⟨ x', hx₁', hx₂' ⟩ := hx₂
              unfold preimage
              simp
              rw [← hx₂']
              unfold h'
              simp
              exact hx₁'
        }
        let s₁ : Set (X ⊕ Y) := {Sum.inl x | x ∈ preimage g₁ s}
        let s₂ : Set (X ⊕ Y) := {Sum.inr y | y ∈ preimage g₂ s}
        have h₄ : IsOpen s₁ := by {
          let f₁ : X → (X ⊕ Y) := fun x ↦ Sum.inl x
          have hf₁ : IsOpenMap f₁ := by exact isOpenMap_inl
          have h₅ : s₁ = image f₁ (preimage g₁ s) := by rfl
          exact hf₁ (⇑g₁ ⁻¹' s) h₁
        }
        have h₅ : IsOpen s₂ := by {
          let f₂ : Y → (X ⊕ Y) := fun y ↦ Sum.inr y
          have hf₂ : IsOpenMap f₂ := by exact isOpenMap_inr
          have h₆ : s₂ = image f₂ (preimage g₂ s) := by rfl
          exact hf₂ (⇑g₂ ⁻¹' s) h₂
        }
        have h₆ : IsOpen (s₁ ∪ s₂) := by exact IsOpen.union h₄ h₅
        rw [h₃]
        exact h₆
      }
    }
  }
  use h''
  constructor
  · constructor
    · ext x
      simp
      rfl
    · ext x
      simp
      rfl
  · intro h''' h₁
    ext x
    match x with
    | Sum.inl x' => {
      calc
      h''' (Sum.inl x') = (h''' ∘ Sum.inl) x' := by rfl
      _= g₁ x' := by rw [h₁.1]
    }
    | Sum.inr y' => {
      calc
      h''' (Sum.inr y') = (h''' ∘ Sum.inr) y' := by rfl
      _= g₂ y' := by rw [h₁.2]
    }
}

/-- The universal property of the quotient space. -/
lemma univ_prop_quotSpace {X Y : Type*} {s : Setoid X}
[TopologicalSpace X] [TopologicalSpace Y]
{f : ContinuousMap X Y}(hf₁ : ∀ x₁ x₂, (s.r x₁ x₂) → f x₁ = f x₂) :
∃! g : ContinuousMap (Quotient s) Y, f = g ∘ Quotient.mk' := by {
  let g : ContinuousMap (Quotient s) Y := {
    toFun := (Quotient.lift f) hf₁
    continuous_toFun := by {
      have h₁ : Continuous f → Continuous (Quot.lift f hf₁) := by exact fun a ↦ continuous_quot_lift hf₁ a
      have h₂ : Continuous f := by exact ContinuousMap.continuous f
      apply h₁ at h₂
      exact h₂
    }
  }
  use g
  constructor
  · simp
    rfl
  · intro g' hg'
    ext x
    have hx : ∃ x' : X, x = Quotient.mk' x' := by {
      refine Quotient.exists.mp ?_
      use x
    }
    obtain ⟨ x', hx' ⟩ := hx
    rw [hx']
    calc
    g' (Quotient.mk' x') = (g' ∘ Quotient.mk') x' := by rfl
    _= f x' := by exact congrFun (id (Eq.symm hg')) x'
    _= (g ∘ Quotient.mk') x' := by rfl
    _= g (Quotient.mk' x') := by rfl
}

/-- The adjunction space is a pushout in the category of topological spaces. -/
lemma univ_prop_adjunctionSpace {X Y Z A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace A]
{f₁ : ContinuousMap A X} {f₂ : ContinuousMap A Y} {g₁ : ContinuousMap X Z} {g₂ : ContinuousMap Y Z}
(hf₁ : Injective f₁) (hf₂ : Injective f₂)(hg : g₁ ∘ f₁ = g₂ ∘ f₂) :
∃! h : ContinuousMap (AdjunctionSpace (f₁ := f₁) (f₂ := f₂) hf₁ hf₂) Z, g₁ = h ∘ (pushout_map_1 hf₁ hf₂) ∧ g₂ = h ∘ (pushout_map_2 hf₁ hf₂) := by {
  have h₁ : ∃! g₃ : ContinuousMap (X ⊕ Y) Z, g₁ = g₃ ∘ Sum.inl ∧ g₂ = g₃ ∘ Sum.inr := by exact univ_prop_coprod g₁ g₂
  obtain ⟨ g₃, h₂, h₃ ⟩ := h₁
  have h₄ : ∃! g₄ : ContinuousMap (AdjunctionSpace (f₁ := f₁) (f₂ := f₂) hf₁ hf₂) Z, g₃ = g₄ ∘ Quotient.mk' (s := equivalence_of_images hf₁ hf₂) := by {
    have h1 : ∀ x₁ x₂, ((equivalence_of_images hf₁ hf₂).r x₁ x₂) → g₃ x₁ = g₃ x₂ := by {
      intro x₁ x₂ hx₁x₂
      simp at hx₁x₂
      obtain h2 | h3 | h4 := hx₁x₂
      · rw [h2]
      · obtain ⟨a, ha⟩ := h3
        rw [← ha.1]
        rw [← ha.2]
        have h3 : g₃ (Sum.inl (f₁ a)) = g₁ (f₁ a) := by {
          rw [h₂.1]
          simp
        }
        have h4 : g₃ (Sum.inr (f₂ a)) = g₂ (f₂ a) := by {
          rw [h₂.2]
          simp
        }
        rw [h3]
        rw [h4]
        calc
        g₁ (f₁ a) = (g₁ ∘ f₁) a := by rfl
        _= (g₂ ∘ f₂) a := by exact congrFun hg a
        _= g₂ (f₂ a) := by rfl
      · obtain ⟨a, ha⟩ := h4
        rw [← ha.1]
        rw [← ha.2]
        calc
        g₃ (Sum.inr (f₂ a)) = (g₃ ∘ Sum.inr) (f₂ a) := by rfl
        _= g₂ (f₂ a) := by rw [h₂.2]
        _= (g₂ ∘ f₂) a := by rfl
        _= (g₁ ∘ f₁) a := by exact congrFun (id (Eq.symm hg)) a
        _= g₁ (f₁ a) := by rfl
        _= (g₃ ∘ Sum.inl) (f₁ a) := by rw [h₂.1]
        _= g₃ (Sum.inl (f₁ a)) := by rfl
    }
    exact univ_prop_quotSpace h1
  }
  obtain ⟨ g₄, h₅, h₆⟩ := h₄
  use g₄
  simp
  constructor
  · constructor
    · ext x
      simp
      have h₇ : g₃ (Sum.inl x) = g₄ (Quotient.mk' (s := equivalence_of_images hf₁ hf₂) (Sum.inl x)) := by {
        rw [h₅]
        simp
      }
      rw [← h₇]
      obtain ⟨ h₈, h₉ ⟩ := h₂
      rw [h₈]
      simp
    · ext x
      simp
      have h₇ : g₃ (Sum.inr x) = g₄ (Quotient.mk' (s := equivalence_of_images hf₁ hf₂) (Sum.inr x)) := by {
        rw [h₅]
        simp
      }
      rw [← h₇]
      obtain ⟨ h₈, h₉ ⟩ := h₂
      rw [h₉]
      simp
  · intro g₄' h₁' h₂'
    ext x
    let g₃' : ContinuousMap (X ⊕ Y) Z := {
      toFun := g₄' ∘ Quotient.mk' (s := equivalence_of_images hf₁ hf₂)
      continuous_toFun := by {
        have h1 : Continuous g₄' := by exact ContinuousMap.continuous g₄'
        let g₅' := fun x ↦ Quotient.mk' (s := equivalence_of_images hf₁ hf₂) x
        have h2 : Continuous g₅' := by exact continuous_quotient_mk'
        exact Continuous.comp h1 h2
    }
    }
    have h₃' : g₁ = g₃' ∘ Sum.inl := by {
      ext x
      unfold g₃'
      simp
      exact congrFun h₁' x
    }
    have h₄' : g₂ = g₃' ∘ Sum.inr := by {
        ext x
        unfold g₃'
        simp
        exact congrFun h₂' x
    }
    have h₅' : g₁ = g₃' ∘ Sum.inl ∧ g₂ = g₃' ∘ Sum.inr := by exact ⟨h₁', h₂'⟩
    have h₆' : g₃' = g₃ := by exact h₃ g₃' h₅'
    have h₇' : g₃ = g₄' ∘ Quotient.mk' (s := equivalence_of_images hf₁ hf₂) := by {
      rw [← h₆']
      rfl
    }
    exact congrFun (congrArg DFunLike.coe (h₆ g₄' h₇')) x
}
