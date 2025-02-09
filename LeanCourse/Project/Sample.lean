import Mathlib

open Function Set Classical
open Topology
open TopologicalSpace

noncomputable section


/-- We define an equivalence relation on the disjoint union of two types X and Y
with respect to a type A, an arbitrary function f₁ : A → X and an injective function f₂ : A → Y:
The equivalence relation is the induced equivalence relation of {incl_X f₁ a ∼ incl_Y f₂ a},
where incl_X and incl_Y are the canonical inclusion maps.  -/
@[simp]
def equivalence_of_images {X Y A : Type*}(f₁ : A → X){f₂ : A → Y}
(hf₂ : Injective f₂) : Setoid (X ⊕ Y) where
  r x y := (x = y) ∨ (∃ a : A, Sum.inl (f₁ a) = x ∧ Sum.inr (f₂ a) = y)
  ∨ (∃ a : A, Sum.inl (f₁ a) = y ∧ Sum.inr (f₂ a) = x) ∨ (∃ a₁ a₂ : A, x = Sum.inr (f₂ a₁) ∧ y = Sum.inr (f₂ a₂) ∧ f₁ a₁ = f₁ a₂)
  -- We define two elements x and y to be equivalent if
      -- they are equal,
      -- they are images of the same element a of A under f₁ and f₂, respectively or
      -- they are images of two different elements a₁, a₂ ∈ A that get mapped to the same element of X under f₁, under f₂
  iseqv := {
    -- the equivalence relation is reflexive by definition
    refl := by simp
     -- we prove symmetry by distinguishing between two cases
    symm := by {
      simp
      intro y₁ y₂ hy₁y₂
      obtain hy₁y₂1 | hy₁y₂2 := hy₁y₂
       --if y₁ = y₂, we have y₂ = y₁ for trivial reasons
      · left
        exact id (Eq.symm hy₁y₂1)
      -- if there exist a₁, a₂ ∈ A with f₂ a₁ = x and f₂ a₂ = y, we can switch the roles of a₁ and a₂ and get y ∼ x
      · obtain ⟨ a₁, ha₁, a₂, ha₂, ha₁a₂ ⟩ := hy₁y₂2
        right
        use a₂
        constructor
        · exact ha₂
        · use a₁
          constructor
          · exact ha₁
          · exact id (Eq.symm ha₁a₂)
    }
    trans := by {
      intro x y z hx hy
      -- We make a case distincion for x ∼ y
      obtain hx₁ | hx₂ | hx₃ | hx₄ := hx
      -- Case 1 : If x = y, transitivity holds for trivial reasons
      · obtain hy₁ | hy₂ | hy₃ | hy₄ := hy
        · rw [hy₁] at hx₁
          left
          exact hx₁
        · obtain ⟨ a, ha ⟩ := hy₂
          right
          left
          rw [← hx₁] at ha
          use a
        · obtain ⟨ a, ha ⟩ := hy₃
          right
          right
          left
          rw [← hx₁] at ha
          use a
        · obtain ⟨ a₁, a₂, ha₁a₂ ⟩ := hy₄
          rw [← hx₁] at ha₁a₂
          right
          right
          right
          use a₁
          use a₂
      -- Case 2 : If there is an a ∈ A with f₁ a = x and f₂ a = y, we make a case distinction for y ∼ z
      · obtain hy₁ | hy₂ | hy₃ | hy₄ := hy
        -- Case 2.1 : If y = z, transitivity holds for trivial reasons
        · obtain ⟨ a, ha⟩ := hx₂
          rw [hy₁] at ha
          right
          left
          use a
        -- Case 2.2 : If there is an a' ∈ A with f₁ a' = y and f₂ a' = z, y has to be both in X and Y, which is a contradiction
        · obtain ⟨ a₁, h₁, h₂⟩ := hx₂
          obtain ⟨ a₂, h₃, h₄ ⟩ := hy₂
          rw [← h₃] at h₂
          have h₅ : Sum.inr (f₂ a₁) ≠ Sum.inl (f₁ a₂) := by exact Sum.inr_ne_inl
          exact False.elim (h₅ h₂)
        -- Case 2.3 : If there is an a' ∈ A with f₁ a' = z and f₂ a' = y, injectivity of f₂ yields a = a', which implies x = z
        · obtain ⟨ a₁, h₁, h₂ ⟩ := hx₂
          obtain ⟨ a₂, h₃, h₄ ⟩ := hy₃
          rw [← h₄] at h₂
          apply Sum.inr_injective at h₂
          apply hf₂ at h₂
          rw [← h₂] at h₃
          rw [h₁] at h₃
          left
          exact h₃
        -- Case 2.4 : Suppose x and y are the images under f₂ of two different elements a₁, a₂ ∈ A that have the same image under f₁
        · obtain ⟨ a, h₁, h₂ ⟩ := hx₂
          obtain ⟨ a₁, a₂, h₃, h₄, h₅ ⟩ := hy₄
          -- In this case, the images f₁ a₁ and f₂ a₂ are both x due to injectivity of f₂
          rw [h₃] at h₂
          apply Sum.inr_injective at h₂
          apply hf₂ at h₂
          -- This implies that f₁ a₂ = x and f₂ a₂ = z, i.e. x ∼ z.
          rw [h₂] at h₁
          rw [h₅] at h₁
          right
          left
          use a₂
          constructor
          · exact h₁
          · exact id (Eq.symm h₄)
      -- Case 3 : If there is an a ∈ A with f₁ a = y and f₂ a = x, we make a case distinction for y ∼ z
      · obtain hy₁ | hy₂ | hy₃ | hy₄ := hy
        -- Case 3.1 : If y = z, transitivity holds for trivial reasons
        · obtain ⟨ a, ha ⟩ := hx₃
          rw [hy₁] at ha
          right
          right
          left
          use a
        -- Case 3.2 : If is an a' ∈ A with f₁ a' = y and f₂ a' = z, x and z are images under f₂ of two different elements a, a' that have the same image (y) under f₁
        · obtain ⟨ a₁, h₁, h₂ ⟩ := hx₃
          obtain ⟨ a₂, h₃, h₄ ⟩ := hy₂
          right
          right
          right
          use a₁
          use a₂
          constructor
          · exact id (Eq.symm h₂)
          · constructor
            · exact id (Eq.symm h₄)
            · rw [← h₃] at h₁
              apply Sum.inl_injective at h₁
              exact h₁
        -- Case 3.3 : If there is an a' ∈ A with f₁ a' = z and f₂ a' = y, y is both in X and Y, which is a contradiction
        · obtain ⟨ a₁, h₁, h₂ ⟩ := hx₃
          obtain ⟨ a₂, h₃, h₄ ⟩ := hy₃
          rw [← h₄] at h₁
          have h₅ : Sum.inl (f₁ a₁) ≠ Sum.inr (f₂ a₂) := by exact Sum.inl_ne_inr
          exact False.elim (h₅ h₁)
        -- Case 3.4 : If y and z are images under two different elements a₁, a₂ ∈ A under f₂, y is both in X and Y, which is a contradiction
        · obtain ⟨ a, h₁, h₂ ⟩ := hx₃
          obtain ⟨ a₁, a₂, h₃, h₄, h₅ ⟩ := hy₄
          rw [h₃] at h₁
          have h₆ : Sum.inl (f₁ a) ≠ Sum.inr (f₂ a₁) := by exact Sum.inl_ne_inr
          exact False.elim (h₆ h₁)
      -- Case 4 : If there are a₁, a₂ ∈ A with f₁ a₁ = f₁ a₂, f₂ a₁ = x and f₂ a₂ = y, we make a case distinction for y ∼ z
      · obtain hy₁ | hy₂ | hy₃ | hy₄ := hy
        -- Case 4.1 : If y = z, transitivity holds for trivial reasons
        · obtain ⟨ a₁, a₂, ha₁a₂ ⟩ := hx₄
          rw [hy₁] at ha₁a₂
          right
          right
          right
          use a₁
          use a₂
        -- Case 4.2 : If there is a ∈ A with f₁ a = y and f₂ a = z, y is both in X and Y, which is a contradiction
        · obtain ⟨ a₁, a₂, h₁, h₂, h₃ ⟩ := hx₄
          obtain ⟨ a, h₄, h₅ ⟩ := hy₂
          rw [h₂] at h₄
          have h₆ : Sum.inl (f₁ a) ≠ Sum.inr (f₂ a₂) := by exact Sum.inl_ne_inr
          exact False.elim (h₆ h₄)
        -- Case 4.3 : Suppose there is an a ∈ A with f₁ a = z and f₂ a = y
        · obtain ⟨ a₁, a₂, h₁, h₂, h₃ ⟩ := hx₄
          obtain ⟨ a, h₄, h₅ ⟩ := hy₃
          rw [h₂] at h₅
          -- then we have a = a₂ due to injectivity of f₂
          apply Sum.inr_injective at h₅
          apply hf₂ at h₅
          -- this implies f₁ a₁ = f₁ a, f₂ a₁ = x and f₂ a = z.
          rw [h₅] at h₄
          rw [← h₃] at h₄
          right
          right
          left
          use a₁
          constructor
          · exact h₄
          · exact id (Eq.symm h₁)
        -- Case 4.4 : Suppose there are a₃, a₄ ∈ A with f₁ a₃ = f₁ a₄, f₂ a₃ = y and f₂ a₄ = z
        · obtain ⟨ a₁, a₂, h₁, h₂, h₃ ⟩ := hx₄
          obtain ⟨ a₃, a₄, h₄, h₅, h₆ ⟩ := hy₄
          rw [h₄] at h₂
          -- then we have a₂ = a₃ due to injectivity of f₂
          apply Sum.inr_injective at h₂
          apply hf₂ at h₂
          -- this implies f₁ a₁ = f₁ a₄, f₂ a₁ = x and f₂ a₄ = z.
          right
          right
          right
          use a₁
          use a₄
          constructor
          · exact h₁
          · constructor
            · exact h₅
            · rw [← h₂] at h₃
              rw [h₆] at h₃
              exact h₃
    }
  }


/-- We define the adjunction space (as a set) as the quotient of X ⊕ Y with respect to the equivalence relation equivalence_of_images. -/
def AdjunctionSpace {X Y A: Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y}
(hf₂ : Embedding f₂) := Quotient (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))


/-- The adjunction space of a topological space is the induced instance of TopologicalSpace on AdjunctionSpace. -/
instance instTopologicalSpaceAdjunction {X Y A: Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂) :
    TopologicalSpace (AdjunctionSpace f₁ hf₂) := by {
      unfold AdjunctionSpace
      infer_instance
    }


/-- The natural map from X (the left space) to the adjunction space -/
@[simp]
def pushout_map_left {X Y A: Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂) :
ContinuousMap X (AdjunctionSpace f₁ hf₂) where
  toFun := fun x ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (Sum.inl x)
  continuous_toFun := by {
    let canon_inj : X → X ⊕ Y := fun x ↦ Sum.inl x
    have h₁ : Continuous canon_inj := by exact continuous_inl
    let quotmap : X ⊕ Y → Quotient (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) := fun x ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x
    have h₂ : Continuous quotmap := by exact continuous_quotient_mk'
    exact Continuous.comp' h₂ h₁
  }


/-- The natural map from Y (the right space) to the adjunction space -/
@[simp]
def pushout_map_right {X Y A: Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂) :
ContinuousMap Y (AdjunctionSpace f₁ hf₂) where
  toFun := fun y ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (Sum.inr y)
  continuous_toFun := by {
    let canon_inj : Y → X ⊕ Y := fun y ↦ Sum.inr y
    have h₁ : Continuous canon_inj := by exact continuous_inr
    let quotmap : X ⊕ Y → Quotient (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) := fun x ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x
    have h₂ : Continuous quotmap := by exact continuous_quotient_mk'
    exact Continuous.comp' h₂ h₁
  }


/-- The disjoint union is the coproduct in the category of topological spaces. -/
theorem univ_prop_coprod {X Y Z : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
(f₁ : ContinuousMap X Z)(f₂ : ContinuousMap Y Z) :
∃! g : ContinuousMap (X ⊕ Y) Z, f₁ = g ∘ Sum.inl ∧ f₂ = g ∘ Sum.inr := by {
  -- Let f₁ : X → Z and f₂ : Y → Z be continuous.
  -- Then we define a function g' : X ⊕ Y → Z that maps all elements originally in X to their image under f₁ and all elements originally in Y to their image under f₂
  let g' : (X ⊕ Y) → Z
    | Sum.inl x => f₁ x
    | Sum.inr y => f₂ y
  -- Proving that g' is continuous:
  let g'' : ContinuousMap (X ⊕ Y) Z := {
    toFun := g'
    continuous_toFun := {
      isOpen_preimage := by {
        -- Let s be open in Z
        intro s hs
        -- Then, the preimages of s under f₁ and f₂ are open
        have h₁ : IsOpen (preimage f₁ s) := by {
          have h_1 : Continuous f₁ := by exact ContinuousMap.continuous f₁
          exact h_1.isOpen_preimage s hs
        }
        have h₂ : IsOpen (preimage f₂ s) := by {
          have h_1 : Continuous f₂ := by exact ContinuousMap.continuous f₂
          exact h_1.isOpen_preimage s hs
        }
        -- The preimage of s under g' is the union of the preimages of s under f₁ and f₂, respectively, considered as a subset of X ⊕ Y.
        have h₃ : preimage g' s = {Sum.inl x | x ∈ preimage f₁ s} ∪ {Sum.inr y | y ∈ preimage f₂ s} := by {
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
              unfold g'
              simp
              exact hx₁'
            · simp at hx₂
              obtain ⟨ x', hx₁', hx₂' ⟩ := hx₂
              unfold preimage
              simp
              rw [← hx₂']
              unfold g'
              simp
              exact hx₁'
        }
        -- Let s₁ and s₂ be the preimages of s under f₁ and f₂, respectively (considered as subsets of X ⊕ Y).
        let s₁ : Set (X ⊕ Y) := {Sum.inl x | x ∈ preimage f₁ s}
        let s₂ : Set (X ⊕ Y) := {Sum.inr y | y ∈ preimage f₂ s}
        -- Then, s₁ and s₂ are open since f₁ and f₂ are continuous.
        have h₄ : IsOpen s₁ := by {
          let g₁ : X → (X ⊕ Y) := fun x ↦ Sum.inl x
          have hg₁ : IsOpenMap g₁ := by exact isOpenMap_inl
          have h₅ : s₁ = image g₁ (preimage f₁ s) := by rfl
          exact hg₁ (⇑f₁ ⁻¹' s) h₁
        }
        have h₅ : IsOpen s₂ := by {
          let g₂ : Y → (X ⊕ Y) := fun y ↦ Sum.inr y
          have hg₂ : IsOpenMap g₂ := by exact isOpenMap_inr
          have h₆ : s₂ = image g₂ (preimage f₂ s) := by rfl
          exact hg₂ (⇑f₂ ⁻¹' s) h₂
        }
        -- This implies that the preimage of s under g'' is open.
        have h₆ : IsOpen (s₁ ∪ s₂) := by exact IsOpen.union h₄ h₅
        rw [h₃]
        exact h₆
      }
    }
  }
  -- Now we prove that g'' is the unique map g with f₁ = g ∘ Sum.inl and f₂ = g ∘ Sum.inr.
  use g''
  constructor
  · constructor
    -- f₁ = g'' ∘ Sum.inl and f₂ = g'' ∘ Sum.inr holds by definition.
    · ext x
      simp
      rfl
    · ext x
      simp
      rfl
  -- It remains to show that every continuous map g''' : X ⊕ Y → Z with f₁ = g''' ∘ Sum.inl and f₂ = g''' ∘ Sum.inr is equal to g''-
  · intro g''' h₁
    ext x
    -- Since every element of X ⊕ Y can either be represented as Sum.inl x or Sum.inr y, g''' and g'' are equal on all elements of X ⊕ Y.
    match x with
    | Sum.inl x' => {
      calc
      g''' (Sum.inl x') = (g''' ∘ Sum.inl) x' := by rfl
      _= f₁ x' := by rw [h₁.1]
    }
    | Sum.inr y' => {
      calc
      g''' (Sum.inr y') = (g''' ∘ Sum.inr) y' := by rfl
      _= f₂ y' := by rw [h₁.2]
    }
}



/-- The universal property of the quotient space. -/
theorem univ_prop_quotSpace {X Y : Type*} {s : Setoid X}
[TopologicalSpace X] [TopologicalSpace Y]
{f : ContinuousMap X Y}(hf₁ : ∀ x₁ x₂, (s.r x₁ x₂) → f x₁ = f x₂) :
∃! g : ContinuousMap (Quotient s) Y, f = g ∘ Quotient.mk' := by {
  -- Let ∼ be an equivalence relation on X and f be a function s.t. for all x₁, x₂ ∈ X with x₁ ∼ x₂ f(x₁) = f(x₂) holds.
  -- Then we define a function g : (X ⧸ ∼) → Y that maps [x] to f(x) (which is well-defined due to the definition of f)
  let g : ContinuousMap (Quotient s) Y := {
    toFun := (Quotient.lift f) hf₁
    -- Since the canonical quotient map is an open map and f is continuous, g is also continuous.
    continuous_toFun := by {
      have h₁ : Continuous f → Continuous (Quot.lift f hf₁) := by exact fun a ↦ continuous_quot_lift hf₁ a
      have h₂ : Continuous f := by exact ContinuousMap.continuous f
      apply h₁ at h₂
      exact h₂
    }
  }
  -- We prove that g is uniquely determined by f = g ∘ Quotient.mk'
  use g
  constructor
  -- f = g ∘ Quotient.mk' holds by definition of g
  · simp
    rfl
  -- Suppose there is a g' with f = g' ∘ Quotient.mk'
  · intro g' hg'
    ext x
    -- Since, every element of (X ⧸ ∼) is of the form [x] with x ∈ X,
    have hx : ∃ x' : X, x = Quotient.mk' x' := by {
      refine Quotient.exists.mp ?_
      use x
    }
    obtain ⟨ x', hx' ⟩ := hx
    rw [hx']
    -- We have g([x]) = g(Quotient.mk' x) = g'(Quotient.mk' x) = g'([x]), which implies that g' and g are equal on all elements of (X ⧸ ∼).
    calc
    g' (Quotient.mk' x') = (g' ∘ Quotient.mk') x' := by rfl
    _= f x' := by exact congrFun (id (Eq.symm hg')) x'
    _= (g ∘ Quotient.mk') x' := by rfl
    _= g (Quotient.mk' x') := by rfl
}



/-- The adjunction space is a pushout in the category of topological spaces. -/
theorem univ_prop_adjunctionSpace {X Y Z A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} {g₁ : ContinuousMap X Z} {g₂ : ContinuousMap Y Z}
(hf₂ : Embedding f₂)(hg : g₁ ∘ f₁ = g₂ ∘ f₂) :
∃! h : ContinuousMap (AdjunctionSpace f₁ hf₂) Z, g₁ = h ∘ (pushout_map_left f₁ hf₂) ∧ g₂ = h ∘ (pushout_map_right f₁ hf₂) := by {
  -- Let X, Y, A be topological spaces, f₁ : A → X continuous and f₂ : A → Y continuous and injective.
  -- Furthermore, let Z be another topological space and g₁ : X → Z and g₂ : Y → Z be continuous maps.
  -- According to the universal property of the disjoint union, there exists a unique continuous map g₃ : (X ⊕ Y) → Z with g₁ = g₃ ∘ Sum.inl and g₂ = g₃ ∘ Sum.inr.
  have h₁ : ∃! g₃ : ContinuousMap (X ⊕ Y) Z, g₁ = g₃ ∘ Sum.inl ∧ g₂ = g₃ ∘ Sum.inr := by exact univ_prop_coprod g₁ g₂
  obtain ⟨ g₃, h₂, h₃ ⟩ := h₁
  -- According to the universal property of the quotient space, there exists a unique continuous map g₄ : AdjunctionSpace f₁ hf₂ → Z with g₃ = g₄ ∘ Quotient.mk'.
  have h₄ : ∃! g₄ : ContinuousMap (AdjunctionSpace f₁ hf₂) Z, g₃ = g₄ ∘ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) := by {
    -- We have to prove that for all x₁, x₂ ∈ X ⊕ Y with x₁ ∼ x₂ with respect to equivalence_of_images, g₃(x₁) = g₃(x₂).
    have h1 : ∀ x₁ x₂, ((equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)).r x₁ x₂) → g₃ x₁ = g₃ x₂ := by {
      -- Let x₁, x₂ ∈ X ⊕ Y with x₁ ∼ x₂ (with respect to equivalence_of_images)
      intro x₁ x₂ hx₁x₂
      simp at hx₁x₂
      -- We make a case distinction for x₁ ∼ x₂:
      obtain h_1 | h_2 | h_3 | h_4 := hx₁x₂
      -- Case 1: If x₁ = x₂, the statement holds for trivial reasons
      · rw [h_1]
      -- Case 2 : There exists a ∈ A s.t. Sum.inl f₁ a = x₁ and Sum.inr f₂ a = x₂
      · obtain ⟨a, ha₁, ha₂⟩ := h_2
        rw [← ha₁, ← ha₂]
        -- We obtain the statement by calculation
        calc
        (g₃ ∘ Sum.inl) (f₁ a) = g₁ (f₁ a) := by rw [h₂.1]
        _= (g₁ ∘ f₁) a := by rfl
        _= (g₂ ∘ f₂) a := by rw [hg]
        _= g₂ (f₂ a) := by rfl
        _= (g₃ ∘ Sum.inr) (f₂ a) := by rw [h₂.2]
      -- Case 3 : There exists a ∈ A s.t. Sum.inl f₁ a = x₂ and Sum.inr f₂ a = x₁
      · obtain ⟨a, ha₁, ha₂⟩ := h_3
        rw [← ha₁, ← ha₂]
        -- We obtain the statement by calculation
        calc
        (g₃ ∘ Sum.inr) (f₂ a) = g₂ (f₂ a) := by rw [h₂.2]
        _= (g₂ ∘ f₂) a := by rfl
        _= (g₁ ∘ f₁) a := by rw [hg]
        _= g₁ (f₁ a) := by rfl
        _= (g₃ ∘ Sum.inl) (f₁ a) := by rw [h₂.1]
      -- Case 4 : There exist a₁, a₂ ∈ A s.t. f₁ a₁ = f₂ a₂, Sum.inl f₂ a₁ = x₁ and Sum.inr f₂ a₂ = x₂
      · obtain ⟨ a₁, ha₁, a₂, ha₂, ha₁a₂ ⟩ := h_4
        rw [ha₁, ha₂]
        -- We obtain the statement by calculation.
        calc
        (g₃ ∘ Sum.inr) (f₂ a₁) = g₂ (f₂ a₁) := by rw [h₂.2]
        _= (g₂ ∘ f₂) a₁ := by rfl
        _= (g₁ ∘ f₁) a₁ := by rw [hg]
        _= g₁ (f₁ a₁) := by rfl
        _= g₁ (f₁ a₂) := by rw [ha₁a₂]
        _= (g₁ ∘ f₁) a₂ := by rfl
        _= (g₂ ∘ f₂) a₂ := by rw [hg]
        _= g₂ (f₂ a₂) := by rfl
        _= (g₃ ∘ Sum.inr) (f₂ a₂) := by rw [h₂.2]
    }
    exact univ_prop_quotSpace h1
  }
  obtain ⟨ g₄, h₅, h₆⟩ := h₄
  -- Now we prove that g₄ is the continuous map uniquely determined by g₁ = g₄ ∘ (pushout_map_left f₁ hf₂) and g₂ = g₄ ∘ (pushout_map_right f₁ hf₂).
  use g₄
  simp
  constructor
  -- g₁ = g₄ ∘ (pushout_map_left f₁ hf₂) and g₂ = g₄ ∘ (pushout_map_right f₁ hf₂) holds by definition of g₄ and pushout_map_left and pushout_map_right, respectively,
  · constructor
    · ext x
      simp
      have h₇ : g₃ (Sum.inl x) = g₄ (Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (Sum.inl x)) := by {
        rw [h₅]
        simp
      }
      rw [← h₇]
      obtain ⟨ h₈, h₉ ⟩ := h₂
      rw [h₈]
      simp
    · ext x
      simp
      have h₇ : g₃ (Sum.inr x) = g₄ (Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (Sum.inr x)) := by {
        rw [h₅]
        simp
      }
      rw [← h₇]
      obtain ⟨ h₈, h₉ ⟩ := h₂
      rw [h₉]
      simp
  -- Suppose g₄' : AdjunctionSpace f₁ hf₂ → Z is continuous with g₁ = g₄' ∘ (pushout_map_left f₁ hf₂) and g₂ = g₄' ∘ (pushout_map_right f₁ hf₂)
  · intro g₄' h₁' h₂'
    ext x
    -- We define g₃' := g₄' ∘ Quotient.mk'. This is a composition of continuous maps and therefore continuous.
    let g₃' : ContinuousMap (X ⊕ Y) Z := {
      toFun := g₄' ∘ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))
      continuous_toFun := by {
        have h1 : Continuous g₄' := by exact ContinuousMap.continuous g₄'
        let g₅' := fun x ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x
        have h2 : Continuous g₅' := by exact continuous_quotient_mk'
        exact Continuous.comp h1 h2
    }
    }
    -- Now, we have g₁ = g₃' ∘ Sum.inl and g₂ = g₃' ∘ Sum.inr by definition of pushout_map_left f₁ hf₂ and pushout_map_right f₁ hf₂.
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
    -- Since g₃ is uniquely determined by g₁ = g₃ ∘ Sum.inl and g₂ = g₃ ∘ Sum.inr, we obtain g₃' = g₃.
    have h₆' : g₃' = g₃ := by exact h₃ g₃' h₅'
    -- Since g₄ is uniquely determined by g₃ = g₄ ∘ Quotient.mk', we obtain g₄ = g₄'.
    have h₇' : g₃ = g₄' ∘ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) := by {
      rw [← h₆']
      rfl
    }
    exact congrFun (congrArg DFunLike.coe (h₆ g₄' h₇')) x
}

/-- The left canonical map of an adjunction space is injective. -/
lemma pushout_map_left_inj {X Y A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂) :
Injective (pushout_map_left f₁ hf₂) := by {
  unfold pushout_map_left
  simp
  unfold Injective
  intro x₁ x₂ hx₁x₂
  simp at hx₁x₂
  have h₁ : (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)).r (Sum.inl x₁) (Sum.inl x₂) := by {
    exact Quotient.eq''.mp hx₁x₂
  }
  unfold equivalence_of_images at h₁
  simp at h₁
  exact h₁
}

/-- The left canonical map of an adjunction space is inducing. -/
lemma pushout_map_left_ind {X Y A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂) :
Inducing (pushout_map_left f₁ hf₂) := by {
  unfold pushout_map_left
  apply inducing_iff_nhds.2
  simp
  intro x
  ext U
  constructor
  · intro hU
    rw [mem_nhds_iff] at hU
    obtain ⟨ V, hV₁, hV₂, hV₃ ⟩ := hU
    unfold Filter.comap
    simp
    by_cases h₁ : x ∈ image f₁ univ
    ·
      sorry
    · sorry
  · sorry
}

/-- The left canonical map of an adjunction space is an embedding. -/
lemma pushout_map_left_embd {X Y A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂) :
Embedding (pushout_map_left f₁ hf₂) := by {
  apply (embedding_iff (pushout_map_left f₁ hf₂)).2
  constructor
  · exact pushout_map_left_ind f₁ hf₂
  · exact pushout_map_left_inj f₁ hf₂
}

/-- If A is closed in Y, the left canonical map of an adjunction space is a closed embedding. -/
lemma pushout_map_left_closedEmbd_if_subspace_closed {X Y A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂) (hA : IsClosed (image f₂ univ)) :
ClosedEmbedding (pushout_map_left f₁ hf₂) := by {
  -- Let A, X and Y be topological spaces, f₁ : A → X be a continuous map and f₂ : A → Y be an embedding. Moreover, let f₂ A be closed in Y.
  -- To prove that the left canonical map into the adjunction space is a closed embedding, we show first that it is a closed map.
  have h_closed : IsClosedMap (pushout_map_left f₁ hf₂) := by {
    unfold IsClosedMap
    -- Let U ⊆ X be closed.
    intro U hU
    -- Then, the preimage of U under f₁ is closed in A since f₁ is continuous.
    have h₁ : IsClosed (preimage f₁ U) := by {
      have h₂ : Continuous f₁ := by exact ContinuousMap.continuous f₁
      exact IsClosed.preimage h₂ hU
    }
    -- Since the image of A under f₂ is closed and f₂ is an embedding, f₂ is a closed embedding.
    have h₂ : ClosedEmbedding f₂ := by {
      apply (closedEmbedding_iff f₂).2
      constructor
      · exact hf₂
      · have h₃ : range f₂ = image f₂ univ := by ext x; unfold range; simp
        rw [h₃]
        exact hA
    }
    -- Hence, the image of f₁⁻¹ U under f₂ is closed in Y.
    have h₃ : IsClosed (image f₂ (preimage f₁ U)) := by {
      exact (ClosedEmbedding.closed_iff_image_closed h₂).mp h₁
    }
    -- By definition of the topology on the disjoint union, the union of Sum.inl U and Sum.inr f₂(f₁⁻¹ U) is closed in X ⊕ Y.
    have h₅ : IsClosed ((image (@Sum.inl X Y) U) ∪ (image (@Sum.inr X Y) (image f₂ (preimage f₁ U)))) := by {
      have h₆ : ClosedEmbedding (@Sum.inl X Y) := by exact closedEmbedding_inl
      have h₇ : ClosedEmbedding (@Sum.inr X Y) := by exact closedEmbedding_inr
      have h₈ : IsClosed (image (@Sum.inl X Y) U) := by exact (ClosedEmbedding.closed_iff_image_closed h₆).mp hU
      have h₉ : IsClosed (image (@Sum.inr X Y) (image f₂ (preimage f₁ U))) := by exact (ClosedEmbedding.closed_iff_image_closed h₇).mp h₃
      exact IsClosed.union h₈ h₉
    }
    let quotmap : (X ⊕ Y) → (AdjunctionSpace f₁ hf₂) := Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))
    -- Now, we prove that the preimage of the image of U under the left canonical map under the quotient map is (Sum.inl U) ∪ (Sum.inr (f₂(f₁⁻¹ U))):
    have h₆ : preimage quotmap (image (pushout_map_left f₁ hf₂) U) = ((image (@Sum.inl X Y) U) ∪ (image (@Sum.inr X Y) (image f₂ (preimage f₁ U)))) := by {
      -- Let x be an arbitrary element of X ⊕ Y.
      ext x
      simp
      constructor
      -- If the image of x under the quotient map is in the image of U under the canonical left map into the adjunction space,
      · intro hx
        obtain ⟨ x', hx'₁, hx'₂ ⟩ := hx
        unfold quotmap at hx'₂
        -- x is equivalent to the image of an element of U with respect to equivalence_of_images.
        apply (Quotient.eq' (s₁ := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))).1 at hx'₂
        simp at hx'₂
        obtain hx'₂1 | hx'₂2 := hx'₂
        -- this implies that x is either the image of an element of U itself
        · left
          use x'
        -- or there is an a ∈ A s.t. f₁(a) ∈ U and Sum.inr(f₂ a) = x, i.e. x ∈ (Sum.inr (f₂(f₁⁻¹ U))).
        · right
          obtain ⟨ a , ha⟩ := hx'₂2
          use a
          rw [ha.1]
          exact And.imp_left (fun a ↦ hx'₁) ha
      -- Now, suppose that x is the image of an element of U or that x ∈ (Sum.inr (f₂(f₁⁻¹ U))).
      · intro hx
        obtain hx₁ | hx₂ := hx
        -- If x ∈ Sum.inl(U), the statement is trivially true.
        · obtain ⟨ x', hx' ⟩ := hx₁
          use x'
          constructor
          · exact hx'.1
          · rw [hx'.2]
        -- If x ∈ (Sum.inr (f₂(f₁⁻¹ U))), x is equivalent to the image of an element of U, which implies the statement.
        · obtain ⟨ x', hx' ⟩ := hx₂
          use f₁ x'
          constructor
          · exact hx'.1
          · rw [← hx'.2]
            unfold quotmap
            apply (Quotient.eq' (s₁ := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))).2
            simp
            use x'
    }
    -- Now, according to the definition of the quotient topology, the image of U under the right canonical map of the adjunction space is closed since the preimage under the quotient map is closed.
    refine isClosed_coinduced.mpr ?_
    unfold quotmap at h₆
    rw [h₆]
    exact h₅
  }
  -- Hence, the right canonical map into the adjunction space is closed and according to a lemma we have proven before, an embedding, so it is a closed embedding.
  apply closedEmbedding_of_embedding_closed
  · exact pushout_map_left_embd f₁ hf₂
  · exact h_closed
}

/-- If A is closed in Y, the right canonical map of the adjunction space restricted to the complement of A is an open embedding. -/
lemma pushout_map_left_restrict_openEmbd_if_subspace_closed {X Y A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂) (hA : IsClosed (image f₂ univ)) :
OpenEmbedding (((image f₂ univ)ᶜ).restrict (pushout_map_right f₁ hf₂)) := by {
  -- Let A, X and Y be topological spaces, f₁ : A → X be a continuous map and f₂ : A → Y be an embedding. Moreover, let f₂ A be closed in Y.
  -- To prove that the restriction of the right canonical map of the adjunction space to the complement of f₂(A) is an open embedding, we prove that it is continuous, injective and an open map.
  apply openEmbedding_iff_continuous_injective_open.2
  constructor
  -- The map is obviuously continuous since the right canonical map of the adjunction space is continuous.
  · have h₁ : Continuous (pushout_map_right f₁ hf₂) := by exact ContinuousMap.continuous (pushout_map_right f₁ hf₂)
    exact Pi.continuous_restrict_apply (⇑f₂ '' univ)ᶜ h₁
  -- Now we prove injectivity:
  · constructor
    · unfold Injective
      -- Let y₁, y₂ ∈ Y \ f₂(A) with (pushout_map_right f₁ hf₂) y₁ = (pushout_map_right f₁ hf₂) y₂.
      intro y₁ y₂ hy₁y₂
      unfold pushout_map_right at hy₁y₂
      simp at hy₁y₂
      -- Then, Sum.inr y₁ and Sum.inr y₂ are equivalent with respect to equivalence_of_images.
      apply (Quotient.eq' (s₁ := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))).1 at hy₁y₂
      -- This means that either y₁ = y₂ or there exist a₁, a₂ ∈ A with f₂ a₁ = y₁ and f₂ a₂ = y₂ and f₁ a₁ = f₂ a₂.
      simp at hy₁y₂
      obtain hy₁y₂1 | hy₁y₂2 := hy₁y₂
      -- The first case is exactly what we wanted to prove.
      · exact SetCoe.ext hy₁y₂1
      -- In the second case, y₁ is in the image of A under f₂, which is a contradiction to the definition of y₁.
      · obtain ⟨ a, h₁, h₂ ⟩ := hy₁y₂2
        have h₃ : (y₁ : Y) ∈ (image f₂ univ) := by simp; use a; exact id (Eq.symm h₁)
        have h₄ : (y₁ : Y) ∈ (image f₂ univ)ᶜ := by exact Subtype.coe_prop y₁
        exact False.elim (h₄ h₃)
    -- Now we prove that the restriction of the right canonical map of the adjunction space to the complement of f₂(A) is an open embedding:
    -- Let U ⊆ Y \ (f₂(A)) be open.
    · intro U hU
      simp
      -- Now, we prove that the preimage of (pushout_map_right f₁ hf₂)(U) under the quotient map equals Sum.inr(U):
      have h₁ : preimage (Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))) (@image (↑(⇑f₂ '' univ)ᶜ) (AdjunctionSpace f₁ hf₂) (fun a ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) ((@Sum.inr X Y) ↑a)) U) = image (@Sum.inr X Y) (U) := by {
        -- Let x be an element of X ⊕ Y.
        ext x
        simp
        constructor
        -- Let x be in the preimage of (pushout_map_right f₁ hf₂)(U) under the quotient map:
        · intro hx
          -- Then, there is an x' ∈ U with Sum.inr x' ∼ x.
          obtain ⟨ x', hx' ⟩ := hx
          use x'
          constructor
          -- x' is obviously not in f₂(A).
          · exact hx'.1
          -- Now, we make a case distinction for the equivalence of Sum.inr x' and x.
          · obtain ⟨hx'₁, hx'₂⟩ := hx'
            obtain h₁ | h₂ | h₃ := hx'₂
            -- If Sum.inr x' = x, this implies the assumption.
            · exact h₁
            -- If there is an a ∈ A with Sum.inl(f₁(a)) = x and f₂(a) = x', x' is in the image of A under f₂, which is a contradiction.
            · obtain ⟨ a, ha₁, ha₂⟩ := h₂
              obtain ⟨ h₁, h₂ ⟩ := hx'₁
              specialize h₁ a
              contradiction
            -- If there exist a₁, a₂ ∈ A with f₂(a₁) = x' and Sum.inr(f₂(a₂)) = x and f₁(a₁) = f₁(a₂), x' is in f₂(A), which is a contradiction.
            · obtain ⟨ h₁, h₂⟩ := hx'₁
              obtain ⟨ a, h₃, h₄⟩ := h₃
              specialize h₁ a
              have h₅ : f₂ a = x' := by exact id (Eq.symm h₃)
              contradiction
        -- Now, let x be in Sum.inr(U).
        · intro hx
          -- Then, there is an x' ∈ U with Sum.inr(x') = x.
          obtain ⟨ x', hx₁, hx₂ ⟩ := hx
          use x'
          -- This implies Quotient.mk'(x) = (pushout_map_right f₁ hf₂)(x'), which is what we wanted to prove.
          constructor
          · exact hx₁
          · left
            exact hx₂
      }
      -- According to the definition of the quotient topology, (pushout_map_right f₁ hf₂)(U) is open if and only if its preimage under the quotient map is open.
      have h₂ : QuotientMap (Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))) := by exact quotientMap_quotient_mk'
      apply QuotientMap.isOpen_preimage at h₂
      -- Since the preimage of (pushout_map_right f₁ hf₂)(U) is Sum.inr(U) and Sum.inr is an open embedding, we are done.
      apply h₂.1
      simp at h₁
      rw [h₁]
      refine (OpenEmbedding.open_iff_image_open ?right.right.hf).mp ?right.right.a
      · exact openEmbedding_inr
      · apply IsClosed.isOpen_compl at hA
        apply IsOpen.isOpenMap_subtype_val at hA
        exact hA U hU
}


/-- The right canonical map of an adjunction space is a quotient map if the map f₁ from the subspace A of Y to X is a quotient map. -/
lemma pushout_map_right_quotmap_if {X Y A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₁ : QuotientMap f₁) (hf₂ : Embedding f₂) :
QuotientMap (pushout_map_right f₁ hf₂) := by {
  -- Let A, X and Y be topological spaces, f₁ : A → X be a quotient map and f₂ : A → Y be an embedding.
  -- To prove that the right canonical map of the adjunction space is a quotient map, we have to prove that it is both surjective and subsets of the adjunction space are open iff their preimage under the right canonical map is open.
  apply quotientMap_iff.2
  simp
  constructor
  -- First, we prove surjectivity.
  · intro x
    -- Since the quotient map from (X ⊕ Y) to AdjunctionSpace f₁ hf₂ is surjective, every element of the Adjunction Space has a preimage x' in X ⊕ Y.
    have hx' : ∃ x' : (X ⊕ Y), Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x' = x := by exact Quotient.exists_rep x
    obtain ⟨ x', hx' ⟩ := hx'
    have hx'' : ∃ x'' : X ⊕ Y, x'' = x' := by use x'
    apply Sum.exists.1 at hx''
    -- We distinguish between two cases: x' is derived from an element of X or x' is derived from an element of Y.
    obtain h₁ | h₂ := hx''
    -- Case 1: Suppose x' is derived from an element of X.
    · obtain ⟨ x'', hx'' ⟩ := h₁
      -- Then, since f₁ is a quotient map and therefore surjective, that element has a preimage a ∈ A.
      apply quotientMap_iff.1 at hf₁
      obtain ⟨ hf₁_1, hf₁_2 ⟩ := hf₁
      specialize hf₁_1 x''
      obtain ⟨ a, ha ⟩ := hf₁_1
      use f₂ a
      simp
      -- Due to the definition of the equivalence relation equivalence_of_images, f₂ a (considered as en element of X ⊕ Y) is equivalent to x'.
      have equiv : (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)).r x' (Sum.inr (f₂ a)) := by {
        simp
        right
        left
        use a
        rw [ha]
        rw [hx'']
        trivial
      }
      -- This implies (pushout_map_right f₁ hf₂) (f₂ a) = x, i.e. x has a preimage under pushout_map_right in Y.
      have h₁ : Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (Sum.inr (f₂ a)) = Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x' := by {
        apply Eq.symm
        apply (Quotient.eq' (s₁ := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))).2
        exact equiv
      }
      rw [h₁]
      exact hx'
    -- Case 2: If x' is derived from an element y ∈ Y, We have pushout_map_right y = x, which is what we wanted to prove.
    · obtain ⟨ x'', hx'' ⟩ := h₂
      use x''
      simp
      rw [hx'', hx']
  -- Now, we prove that a set in the adjunction space is open iff its preimage under pushout_map_right is open.
  · intro s
    constructor
    -- '=>' immediately follows from the continuity of pushout_map_right.
    · intro hs
      have hcont : Continuous (pushout_map_right f₁ hf₂) := by exact ContinuousMap.continuous (pushout_map_right f₁ hf₂)
      exact hcont.isOpen_preimage s hs
    -- '<=': Let s be a set in the adjunction space that has an open preimage under the right canonical map.
    · intro h₁
      -- Let s₁ and s₂ be the preimages of s under the left canonical map and the right canonical map, respectively.
      let s₁ : Set X := preimage (pushout_map_left f₁ hf₂) s
      let s₂ : Set Y := preimage (pushout_map_right f₁ hf₂) s
      -- Then, s₂ is open by definition and since f₂ is continuous, the preimage of s₂ under f₂ is open as well.
      have hs₂ : IsOpen s₂ := by unfold s₂; exact h₁
      have hf₂' : Continuous f₂ := by exact ContinuousMap.continuous f₂
      have hfs₂A : IsOpen (preimage f₂ s₂) := by exact hf₂'.isOpen_preimage s₂ h₁
      apply quotientMap_iff.1 at hf₁
      obtain ⟨ hf₁_1, hf₁_2 ⟩ := hf₁
      specialize hf₁_2 s₁
      -- Since for all a ∈ A, Sum.inl(f₁(a)) and Sum.inr(f₂(a)) are equivalent with respect to equivalence_of_images, f₂⁻¹ s₂ and f₁⁻¹ s₁ are equal.
      have h₂ : preimage f₂ s₂ = preimage f₁ s₁ := by {
        ext x
        constructor
        · intro h₃
          unfold s₂ at h₃
          simp at h₃
          have h₄ : (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)).r (Sum.inr (f₂ x)) (Sum.inl (f₁ x)) := by {
            simp
            use x
          }
          have h₅ : Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (Sum.inr (f₂ x)) = Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (Sum.inl (f₁ x))  := by {
            apply (Quotient.eq' (s₁ := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))).2
            exact h₄
          }
          rw [h₅] at h₃
          unfold s₁
          simp
          exact h₃
        · intro h₃
          unfold s₁ at h₃
          simp at h₃
          have h₄ : (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)).r (Sum.inl (f₁ x)) (Sum.inr (f₂ x)) := by {
            simp
            use x
          }
          have h₅ : Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (Sum.inl (f₁ x)) = Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (Sum.inr (f₂ x))  := by {
            apply (Quotient.eq' (s₁ := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))).2
            exact h₄
          }
          rw [h₅] at h₃
          unfold s₂
          simp
          exact h₃
      }
      -- This implies that f₁⁻¹ s₁ is open. Since f₁ is a quotient map, this also implies that s₁ is open.
      rw [← h₂] at hf₁_2
      apply hf₁_2.2 at hfs₂A
      have h1 : IsOpen (image (@Sum.inl X Y) s₁) := by apply isOpenMap_inl; exact hfs₂A
      have h2 : IsOpen (image (@Sum.inr X Y) s₂) := by apply isOpenMap_inr; exact h₁
      let quotmap : (X ⊕ Y) → AdjunctionSpace f₁ hf₂ := Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))
      -- Now, we can write the preimage of s under Quotient.mk' as Sum.inl(s₁) ∪ Sum.inr(s₂).
      have h3 : preimage quotmap s = (image (@Sum.inl X Y) s₁) ∪ (image (@Sum.inr X Y) s₂) := by {
        unfold quotmap; unfold s₁; unfold s₂
        simp
        ext x
        constructor
        · intro hx
          simp at hx
          have hx₁ : ∃ x₁ : X ⊕ Y, Quotient.mk' (s := equivalence_of_images f₁ _) x₁ ∈ s ∧ x₁ = x := by use x
          apply Sum.exists.1 at hx₁
          obtain hx₁1 | hx₁2 := hx₁
          · left
            simp
            exact hx₁1
          · right
            simp
            exact hx₁2
        · intro hx
          simp at hx
          simp
          obtain hx₁ | hx₂ := hx
          · obtain ⟨ x₁, hx₁1, hx₁2 ⟩ := hx₁
            rw [← hx₁2]
            exact hx₁1
          · obtain ⟨ x₂, hx₂1, hx₂2 ⟩ := hx₂
            rw [← hx₂2]
            exact hx₂1
      }
      -- Since s₁ and s₂ are open, Sum.inl(s₁) ∪ Sum.inr(s₂) is open as well. This implies, since Quotient.mk' is a quotient map, that s is open as well.
      have h4 : IsOpen ((image (@Sum.inl X Y) s₁) ∪ (image (@Sum.inr X Y) s₂)) := by exact IsOpen.union h1 h2
      rw [← h3] at h4
      exact h4
}

/-- A topological space X is preconnected if and only if the only subsets of X that are clopen are ∅ and X.-/
theorem preconnectedSpace_iff_clopen {X : Type*} [TopologicalSpace X]:
    PreconnectedSpace X ↔ ∀ s : Set X, IsClopen s → s = ∅ ∨ s = Set.univ :=
  ⟨fun _ s hs ↦ isClopen_iff.mp hs, fun h ↦ ⟨fun u v hu hv huv huu hvv ↦ by
    apply Set.nonempty_iff_ne_empty.mpr
    intro hdj
    have h : uᶜ = v := by
      apply subset_antisymm
      · apply Set.compl_subset_iff_union.mpr
        exact Set.eq_univ_of_univ_subset huv
      · apply Disjoint.subset_compl_left
        apply Set.disjoint_iff_inter_eq_empty.mpr
        rwa [Set.univ_inter] at hdj
    subst h
    obtain rfl | rfl := h u ⟨⟨hv⟩, hu⟩
    · simp at huu
    · simp at hvv⟩⟩

/-- The adjunction space is open if both spaces X and Y it is derived from are open.-/
lemma adjunction_connected_if_comps_connected {X Y A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂)
(hA : Nonempty A) (hX : ConnectedSpace X) (hY : ConnectedSpace Y) :
ConnectedSpace (AdjunctionSpace f₁ hf₂) where
-- Let A be a nonempty topological space, X and Y be connected topological spaces, f₁ : A → X be a continuous map and f₂ : A → Y be an embedding.
-- Then, we prove that the adjunction space is also connected.
-- At first, we prove that the adjunction space is preconnected:
  isPreconnected_univ := by {
    -- Since X and Y are connected, they are also preconnected.
    have hX : PreconnectedSpace X := by exact ConnectedSpace.toPreconnectedSpace
    have hY : PreconnectedSpace Y := by exact ConnectedSpace.toPreconnectedSpace
    refine preconnectedSpace_iff_univ.mp ?_
    apply preconnectedSpace_iff_clopen.2
    -- Let s be a clopen subset of the adjunction space.
    -- We have to prove that s = ∅ or s = univ.
    intro s hs
    obtain ⟨ hs₁, hs₂ ⟩ := hs
    -- Let s' be the preimage of s under the quotient map.
    let s' : Set (X ⊕ Y) := preimage (@Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))) s
    -- Then, s' is open and closed since the quotient map is continuous.
    have hs' : IsClopen s' := by {
      have h₁ := continuous_quotient_mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))
      have h₂ : ∀ (s : Set (Quotient (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)))), IsClosed s → IsClosed (Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) ⁻¹' s) := by apply continuous_iff_isClosed.1 at h₁; exact h₁
      specialize h₂ s
      apply h₂ at hs₁
      apply Continuous.isOpen_preimage at h₁
      specialize h₁ s
      apply h₁ at hs₂
      unfold s'; unfold IsClopen
      exact ⟨hs₁, h₁ (h₁ (h₁ (h₁ hs₂)))⟩
    }
    obtain ⟨ hs'₁, hs'₂ ⟩ := hs'
    -- According to the definition of the quotient space topology, the preimage of s' under Sum.inl and Sum.inr are closed and open as well.
    apply isClosed_sum_iff.1 at hs'₁
    apply isOpen_sum_iff.1 at hs'₂
    obtain ⟨ hs'₁1, hs'₁2 ⟩ := hs'₁
    obtain ⟨ hs'₂1, hs'₂2 ⟩ := hs'₂
    have hs'_left : IsClopen (preimage (@Sum.inl X Y) s') := ⟨ hs'₁1, hs'₂1 ⟩
    have hs'_right : IsClopen (preimage (@Sum.inr X Y) s') := ⟨ hs'₁2, hs'₂2 ⟩
    -- Since X is preconnected, the preimage of s' under Sum.inl is either ∅ or X.
    apply preconnectedSpace_iff_clopen.1 at hs'_left
    -- Analogously, since Y is preconnected, the preimage of s' under Sum.inr is either ∅ or Y.
    apply preconnectedSpace_iff_clopen.1 at hs'_right
    obtain left_empty | left_univ := hs'_left
    · obtain right_empty | right_univ := hs'_right
      -- If Sum.inl⁻¹ s' = ∅ and Sum.inr⁻¹ s' = ∅, we get s' = by definition of the topology of the disjoint union.
      · have h_empty : s' = ∅ := by {
          ext x
          cases x
          · constructor
            · intro h
              rename_i x₁
              have h' : x₁ ∈ preimage (@Sum.inl X Y) s' := by exact h
              rw [left_empty] at h'
              exact h'
            · apply False.elim
          · constructor
            · rename_i x₂
              intro h
              have h' : x₂ ∈ preimage (@Sum.inr X Y) s' := by exact h
              rw [right_empty] at h'
              exact h'
            · apply False.elim
        }
        unfold s' at h_empty
        -- This implies s = ∅ by definition of s'.
        left
        have h₁ : Surjective (Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))) := by exact surjective_quotient_mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (X ⊕ Y)
        ext x
        constructor
        · intro hx
          have hx' : ∃ x', Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x' = x := by exact h₁ x
          obtain ⟨ x', hx' ⟩ := hx'
          have hx'' : x' ∈ preimage (Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))) s := by simp; rw [hx']; exact hx
          rw [h_empty] at hx''
          contradiction
        · intro hx
          contradiction
    -- Suppose Sum.inl⁻¹ s' = ∅ and Sum.inr⁻¹ s' = Y.
      · apply exists_true_iff_nonempty.2 at hA
        -- Let a be an arbitrary element of A (exists since A is nonempty)
        obtain ⟨ a, ha ⟩ := hA
        -- Then, f₁(a) ∉ Sum.inl⁻¹(s') since Sum.inl⁻¹(s') = ∅.
        have ha₁ : f₁ a ∉ preimage (@Sum.inl X Y) s' := by rw [left_empty]; exact fun a ↦ a
        -- Moreover, f₂(a) ∈ Y = Sum.inr⁻¹(s').
        have ha₂ : f₂ a ∈ preimage (@Sum.inr X Y) s' := by rw [right_univ]; trivial
        simp at ha₁; simp at ha₂
        -- By definition of s', this implies that the image of f₁(a) under the canonical left map into the adjunction space is not an element of s.
        have ha₃ : (pushout_map_left f₁ hf₂) (f₁ a) ∉ s := by {
          unfold pushout_map_left; simp
          unfold s' at ha₁; simp at ha₁
          exact ha₁
        }
        -- Similarly, the image of f₂(a) under the canonical right map into the adjunction space is an element of s.
        have ha₄ : (pushout_map_right f₁ hf₂) (f₂ a) ∈ s := by {
          unfold pushout_map_right; simp
          unfold s' at ha₂; simp at ha₂
          exact ha₂
        }
        -- But by definition of equivalence_of_images, Sum.inl(f₁(a)) and Sum.inr(f₂(a)) are equivalent with respect to equivalence_of_images.
        have ha₅ : (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)).r ((@Sum.inl X Y) (f₁ a)) ((@Sum.inr X Y) (f₂ a)) := by simp; use a
        -- This implies that the image of f₁(a) under the canonical left map equals the image of f₂(a) under the canonical right map, contradiction.
        have ha₆ : (pushout_map_left f₁ hf₂) (f₁ a) = (pushout_map_right f₁ hf₂) (f₂ a) := by {
          unfold pushout_map_left; unfold pushout_map_right; simp
          apply (@Quotient.eq' (X ⊕ Y) (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) ((@Sum.inl X Y) (f₁ a)) ((@Sum.inr X Y) (f₂ a))).2 at ha₅
          exact ha₅
        }
        rw [ha₆] at ha₃
        contradiction
    · obtain right_empty | right_univ := hs'_right
    -- Suppose Sum.inl⁻¹(s') = X and Sum.inr⁻¹(s') = ∅.
      · apply exists_true_iff_nonempty.2 at hA
        -- Let a be an arbitrary element of A (exists since A is nonempty)
        obtain ⟨ a, ha ⟩ := hA
        -- Then, Sum.inl⁻¹(f₁(a)) ∈ s' since Sum.inl⁻¹(s') = X.
        have ha₁ : f₁ a ∈ univ := by trivial
        rw [← left_univ] at ha₁
        simp at ha₁
        -- Moreover, f₂(a) ∉ Sum.inr⁻¹(s') since Sum.inr⁻¹(s') = Y.
        have ha₂ : f₂ a ∉ preimage (@Sum.inr X Y) s' := by rw [right_empty]; exact fun a ↦ a
        -- That implies that the image of f₁(a) under the left canonical map into the adjunction space is in s...
        have ha₃ : (pushout_map_left f₁ hf₂) (f₁ a) ∈ s := by {
          unfold pushout_map_left; simp
          unfold s' at ha₁; simp at ha₁
          exact ha₁
        }
        -- and the image of f₂(a) under the right canonical map into the adjunction space is not in s.
        have ha₄ : (pushout_map_right f₁ hf₂) (f₂ a) ∉ s := by {
          unfold pushout_map_right; simp
          unfold s' at ha₂; simp at ha₂
          exact ha₂
        }
        -- But according to the definition of equivalence_of_images, Sum.inl(f₁(a)) and Sum.inr(f₂(a)) are equivalent.
        have ha₅ : (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)).r ((@Sum.inl X Y) (f₁ a)) ((@Sum.inr X Y) (f₂ a)) := by simp; use a
        -- Hence, the image of f₁(a) under the canonical left map into the adjunction space and the image of f₂(a) under the canonical right map into the adjunction space are equal.
        have ha₆ : (pushout_map_left f₁ hf₂) (f₁ a) = (pushout_map_right f₁ hf₂) (f₂ a) := by {
          unfold pushout_map_left; unfold pushout_map_right; simp
          apply (@Quotient.eq' (X ⊕ Y) (equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) ((@Sum.inl X Y) (f₁ a)) ((@Sum.inr X Y) (f₂ a))).2 at ha₅
          exact ha₅
        }
        -- This is a contradiction.
        rw [ha₆] at ha₃
        contradiction
      -- Suppose Sum.inl⁻¹(s') = X and Sum.inr⁻¹(s') = Y. Then, every element of X ⊕ Y is in s'.
      · right
        ext x
        -- Since the quotient map is surjective, every element of the adjunction space is an element of Quotient.mk'(s') = s.
        have h₁ := surjective_quotient_mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (X ⊕ Y) x
        obtain ⟨ x', hx'⟩ := h₁
        constructor
        · intro h; trivial
        · intro h
          rw [← hx']
          cases x'
          · rename_i x''
            have h₁ : x'' ∈ univ := by trivial
            rw [← left_univ] at h₁
            unfold s' at h₁; simp at h₁
            exact h₁
          · rename_i x''
            have h₁ : x'' ∈ univ := by trivial
            rw [← right_univ] at h₁
            unfold s' at h₁; simp at h₁
            exact h₁
    · exact hY
    · exact hX
  }
  -- Now, we are going to prove that the adjunction space is nonempty:
  toNonempty := by {
    -- Let a be an arbitrary element of A (exists because A is nonempty).
    rw [← exists_true_iff_nonempty]
    rw [← exists_true_iff_nonempty] at hA
    obtain ⟨ a, ha ⟩ := hA
    -- This implies that Quotient.mk'(Sum.inl(f₁(a))) is an element of the adjunction space.
    let x := @Sum.inl X Y (f₁ a)
    use Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x
  }


/-- The adjunction space is a T₁-space if both X and Y are T₁ and f₂(A) is closed in Y. -/
lemma adjunction_t1_if_comps_t1 {X Y A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂)
(hX : T1Space X) (hY : T1Space Y) (hA : IsClosed (image f₂ univ)) :
T1Space (AdjunctionSpace f₁ hf₂) where
-- Let A be a topological space, X and Y be T₁-spaces, f₁ : A → X be continuous, f₂ : A → Y be an embedding and f₂(A) be closed.
  t1 := by {
    -- Let x be an arbitrary element of the adjunction space. We have to prove that {x} is closed.
    intro x
    unfold AdjunctionSpace at x
    let quotmap : X ⊕ Y → AdjunctionSpace f₁ hf₂ := fun x ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x
    -- Let S be the preimage of {x} under the quotient map. Then, it suffices to prove that S is closed.
    let S : Set (X ⊕ Y) := preimage quotmap {x}
    have h₁ : IsClosed S → IsClosed {x} := by {
      intro h
      exact isClosed_coinduced.mpr h
    }
    -- Let S_1 be the preimage of {x} under the left canonical map into the adjunction space.
    let S_1 : Set X := preimage (pushout_map_left f₁ hf₂) {x}
    have h₃ : IsClosed S_1 := by {
      -- Then, we distinguish between two cases:
      by_cases h₃ : S_1 = ∅
      -- Case 1 : S_1 is empty. Then, S_1 is trivially closed.
      · rw [h₃]
        exact isClosed_empty
      -- Case 2: S_1 is not empty.
      · -- First, we prove that there exists a unique element x' ∈ S_1.
        have h₄ : ∃! x : X, x ∈ S_1 := by {
          -- Since S_1 is nonempty, there exists an x' ∈ S_1.
          have h₅ : ∃ x : X, x ∈ S_1 := by {
            by_contra h₆
            have h₇ : S_1 = ∅ := by exact preimage_singleton_eq_empty.mpr h₆
            contradiction
          }
          obtain ⟨ x', hx' ⟩ := h₅
          use x'
          simp
          -- Now, we have to prove that for every y ∈ S_1, y = x'.
          constructor
          · exact hx'
          · intro y hy
            -- Since x' and y are both in S_1, their images under the canonical left map into the pushout are equal.
            -- This implies Sum.inl(x') and Sum.inl(y) are equivalent with respect to equivalence_of_images.
            unfold S_1 at hy
            simp at hy
            unfold S_1 at hx'
            simp at hx'
            rw [← hx'] at hy
            apply (Quotient.eq' (s₁ := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))).1 at hy
            -- According to the definition of equivalence_of_images, this implies that x' and y are equal.
            simp at hy
            exact hy
        }
        -- This implies that S_1 is of the form {x''}.
        obtain ⟨x'', hx''⟩ := h₄
        have h₅ : S_1 = {x''} := by exact eq_singleton_iff_unique_mem.mpr hx''
        rw [h₅]
        -- Since X is a T₁-space, S_1 is closed.
        exact isClosed_singleton
    }
    -- Now, let S_2 be the preimage of {x} under the right canonical map into the adjunction space.
    let S_2 : Set Y := preimage (pushout_map_right f₁ hf₂) {x}
    -- Now, we are going to prove that S_2 is closed.
    have h₄ : IsClosed S_2 := by {
      -- We distinguish between two cases:
      by_cases h_empty : S_2 = ∅
      -- If S_2 is empty, S_2 is trivially closed.
      · rw [h_empty]
        exact isClosed_empty
      -- If S_2 is nonempty, we distinguish between two cases again:
      · by_cases h_singleton : ∃! y : Y, y ∈ S_2
        -- If there is exactly one element in S_2, S_2 is closed since Y is T₁.
        · have h₅ : ∃ y : Y, y ∈ S_2 := by {
            by_contra h₆
            have h₇ : S_2 = ∅ := by exact preimage_singleton_eq_empty.mpr h₆
            contradiction
          }
          obtain ⟨y, hy⟩ := h_singleton
          have h₆ : S_2 = {y} := by exact eq_singleton_iff_unique_mem.mpr hy
          rw [h₆]
          exact isClosed_singleton
        -- If there is more than one element in S_2, we prove that S_2 is the image under f₂ of the preimage of S_2 under f₁.
        · have h₅ : S_2 = image f₂ (preimage f₁ S_1) := by {
            -- Let y be an arbitrary element of Y.
            ext y
            unfold S_1; unfold S_2; unfold pushout_map_left; unfold pushout_map_right
            simp
            constructor
            -- First, suppose y ∈ S_2.
            · intro hy
              -- Then, there is an element y' ∈ Y with y' ∈ S_2 and y' ≠ y.
              have h₄ : ∃ y' : Y, y' ∈ S_2 ∧ y' ≠ y := by {
                by_contra h₅
                push_neg at h₅
                have h₆ : ∃! y, y ∈ S_2 := by {
                  use y
                  simp
                  constructor
                  · exact hy
                  · exact fun y a ↦ h₅ y a
                }
                contradiction
              }
              obtain ⟨ y', hy'₁, hy'₂ ⟩ := h₄
              unfold S_2 at hy'₁; simp at hy'₁
              rw [← hy'₁] at hy
              -- This implies that Sum.inr(y) and Sum.inr(y') are equivalent with respect to equivalence_of_images.
              apply (Quotient.eq' (s₁ := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))).1 at hy
              -- By definition of the equivalence_of_images, y and y' are either equal or images under f₂ of some elements a₁ and a₂ with the same image under f₁.
              simp at hy
              obtain hy₁ | hy₂ := hy
              -- y = y' is a contradiction to the definition of y'.
              · exact False.elim (hy'₂ (id (Eq.symm hy₁)))
              -- If there exist a₁, a₂ ∈ A with f₂ a₁ = y, f₂ a₂ = y' and f₁ a₁ = f₁ a₁, f₁ a₁ is apparently in S_1, which implies that y = f₂ a₁ is in f₂ (f₁⁻¹ S_1).
              · obtain ⟨ a₁, ha₁, a₂, ha₂, ha₁a₂ ⟩ := hy₂
                use a₁
                constructor
                · rw [← hy'₁]
                  apply (Quotient.eq' (s₁ := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))).2
                  simp
                  use a₂
                  constructor
                  · exact id (Eq.symm ha₁a₂)
                  · exact id (Eq.symm ha₂)
                · exact id (Eq.symm ha₁)
            -- Now, let y be in f₂ (f₁⁻¹ S_1).
            · intro hy
              -- Then, there is an a ∈ f₁⁻¹ S_1 with f₂(a) = y.
              obtain ⟨ a, ha ⟩ := hy
              rw [← ha.2, ← ha.1]
              -- This implies that Sum.inr(f₂(a)) and Sum.inl(y) = Sum.inl(f₁(a)) are equivalent, hence y ∈ S_2.
              apply (Quotient.eq' (s₁ := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))).2
              simp
              use a
          }
          rw [h₅]
          -- Since f₁ is continuous, f₁⁻¹ (S_1) is closed.
          have h₆ : Continuous f₁ := by exact ContinuousMap.continuous f₁
          have h₇ : IsClosed (preimage f₁ S_1) := by exact IsClosed.preimage h₆ h₃
          -- Since f₂ is an embedding and f₂(A) is closed, f₂ is a closed embedding and therefore a closed map.
          have h₈ : ClosedEmbedding f₂ := by {
            apply (closedEmbedding_iff f₂).2
            constructor
            · exact hf₂
            · have h₈ : range f₂ = image f₂ univ := by ext x; unfold range; simp
              rw [h₈]
              exact hA
          }
          have h₉ : IsClosedMap f₂ := by exact ClosedEmbedding.isClosedMap h₈
          -- This implies that f₂(f₁⁻¹(S_1)) = S_2 is closed, which is what we wanted to prove.
          exact h₉ (⇑f₁ ⁻¹' S_1) h₇
      }
    -- Now, according to the definition of the canonical maps of the adjunction space we have S = Sum.inl(S_1) ∪ Sum.inr(S_2).
    have h₅ : (image (@Sum.inl X Y) (S_1)) ∪ (image (@Sum.inr X Y) (S_2)) = S := by {
      unfold S
      ext x'
      constructor
      · intro h₉
        obtain h1 | h2 := h₉
        · obtain ⟨ s₁, hs₁ ⟩ := h1
          obtain ⟨ hs₁1, hs₁2⟩ := hs₁
          exact mem_of_eq_of_mem (id (Eq.symm hs₁2)) hs₁1
        · obtain ⟨ s₂, hs₂ ⟩ := h2
          obtain ⟨ hs₂1, hs₂2 ⟩ := hs₂
          exact mem_of_eq_of_mem (id (Eq.symm hs₂2)) hs₂1
      · intro h₉
        have h1 : ∃ x'' : X ⊕ Y, x'' = x' := by use x'
        have h2 : (∃ x'' : X ⊕ Y, x'' = x') ↔ ((∃ x₁, Sum.inl x₁ = x') ∨ (∃ y₁, Sum.inr y₁ = x')) := by {
          exact Sum.exists
        }
        apply h2.1 at h1
        obtain h3 | h4 := h1
        · obtain ⟨ x₁, hx₁⟩ := h3
          have h5 : x₁ ∈ S_1 := by unfold S_1; simp; rw [hx₁]; exact h₉
          have h6 : x' ∈ image (@Sum.inl X Y) S_1 := by use x₁
          exact mem_union_left (Sum.inr '' S_2) h6
        · obtain ⟨ x₂, hx₂ ⟩ := h4
          have h5 : x₂ ∈ S_2 := by unfold S_2; simp; rw [hx₂]; exact h₉
          have h6 : x' ∈ image (@Sum.inr X Y) S_2 := by use x₂
          exact mem_union_right (Sum.inl '' S_1) h6
    }
    -- Since S_1 and S_2 are closed and Sum.inl and Sum.inr are closed embeddings, S = Sum.inl(S_1) ∪ Sum.inr(S_2) is closed in X ⊕ Y.
    have h₆ : IsClosed S := by {
      rw [← h₅]
      have h₆ : ClosedEmbedding (@Sum.inl X Y) := by exact closedEmbedding_inl
      have h₇ : IsClosedMap (@Sum.inl X Y) := by exact ClosedEmbedding.isClosedMap h₆
      have h₈ : IsClosed (image (@Sum.inl X Y) S_1) := by exact h₇ S_1 h₃
      have h₉ : ClosedEmbedding (@Sum.inr X Y) := by exact closedEmbedding_inr
      have h₁₀ : IsClosedMap (@Sum.inr X Y) := by exact ClosedEmbedding.isClosedMap h₉
      have h₁₁ : IsClosed (image (@Sum.inr X Y) S_2) := by exact h₁₀ S_2 h₄
      exact IsClosed.union (h₇ S_1 h₃) (h₁₀ S_2 h₄)
    }
    -- Hence, {x} = Quotient.mk'(S) is closed.
    apply h₁ at h₆
    exact h₆
  }
