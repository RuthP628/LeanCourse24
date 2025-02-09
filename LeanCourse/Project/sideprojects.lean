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

lemma TietzeExtension_restricts_eqOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
[NormalSpace X] [self: TietzeExtension.{u_1} Y] (s : Set X) (hs : IsClosed s) (f : X → Y) (hf: ContinuousOn f s) :
∃ g : ContinuousMap X Y, s.EqOn f g := by {
  let f' : ContinuousMap s Y := {
    toFun := fun x ↦ f x
    continuous_toFun := by {
      apply continuousOn_iff_continuous_restrict.1 at hf
      exact hf
    }
  }
  have h : ∃ (g : C(X, Y)), g.restrict s = f' := by {
    apply TietzeExtension.exists_restrict_eq'
    exact hs
  }
  obtain ⟨ g, hg ⟩ := h
  use g
  unfold EqOn
  intro x hx
  calc
  f x = f' ⟨x, hx⟩ := by rfl
  _= g x := by rw [← hg]; rfl
}

lemma adjunction_t4_if_comps_t4 {X Y A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂)
(hX : T4Space X) (hY : T4Space Y) (hA : IsClosed (image f₂ univ)) :
T4Space (AdjunctionSpace f₁ hf₂) where
  t1 := by {
    have hX₁ : T1Space X := by exact T4Space.toT1Space
    have hY₁ : T1Space Y := by exact T4Space.toT1Space
    have h₁ : T1Space (AdjunctionSpace f₁ hf₂) := by exact adjunction_t1_if_comps_t1 f₁ hf₂ hX₁ hY₁ hA
    exact fun x ↦ isClosed_singleton
  }
  normal := by {
    intro s t hs ht hst
    let s₁ := preimage (pushout_map_left f₁ hf₂) s
    let t₁ := preimage (pushout_map_left f₁ hf₂) t
    let s₂ := preimage (pushout_map_right f₁ hf₂) s
    let t₂ := preimage (pushout_map_right f₁ hf₂) t
    let U := s₁ ∪ t₁
    let V := s₂ ∪ t₂
    have hs₁ : IsClosed s₁ := by {
      unfold s₁; unfold pushout_map_left; simp
      have h₁ : QuotientMap fun x ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x := by exact quotientMap_quotient_mk'
      apply QuotientMap.isClosed_preimage at h₁
      apply h₁.2 at hs
      apply isClosed_sum_iff.1 at hs
      exact hs.1
    }
    have ht₁ : IsClosed t₁ := by {
      unfold t₁; unfold pushout_map_left; simp
      have h₁ : QuotientMap fun x ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x := by exact quotientMap_quotient_mk'
      apply QuotientMap.isClosed_preimage at h₁
      apply h₁.2 at ht
      apply isClosed_sum_iff.1 at ht
      exact ht.1
    }
    have hs₂ : IsClosed s₂ := by {
      unfold s₂; unfold pushout_map_right; simp
      have h₁ : QuotientMap fun x ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x := by exact quotientMap_quotient_mk'
      apply QuotientMap.isClosed_preimage at h₁
      apply h₁.2 at hs
      apply isClosed_sum_iff.1 at hs
      exact hs.2
    }
    have ht₂ : IsClosed t₂ := by {
      unfold t₂; unfold pushout_map_right; simp
      have h₁ : QuotientMap fun x ↦ Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x := by exact quotientMap_quotient_mk'
      apply QuotientMap.isClosed_preimage at h₁
      apply h₁.2 at ht
      apply isClosed_sum_iff.1 at ht
      exact ht.2
    }
    have hs₁t₁ : IsClosed U := by unfold U; exact IsClosed.union hs₁ ht₁
    have hs₂t₂ : IsClosed V := by unfold V; exact IsClosed.union hs₂ ht₂
    have hs₁t₁' : Disjoint s₁ t₁ := by {
      apply Set.disjoint_iff_inter_eq_empty.2
      apply Set.disjoint_iff_inter_eq_empty.1 at hst
      ext x
      constructor
      · intro hx
        obtain ⟨ hx₁, hx₂ ⟩ := hx
        unfold s₁ at hx₁; unfold t₁ at hx₂
        simp at hx₁; simp at hx₂
        have h₁ : Quotient.mk' (s := equivalence_of_images f₁ _) ((@Sum.inl X Y) x) ∈ s ∩ t := by exact mem_inter hx₁ hx₂
        rw [hst] at h₁
        exact h₁
      · intro hx
        exact False.elim hx
    }
    let a : X → ℝ :=  fun x ↦ if h : x ∈ s₁ then 1 else 0
    have ha : ContinuousOn a U := by {
        refine continuousOn_iff.mpr ?_
        intro x hx t ht hxt
        by_cases ht' : ¬ 1 ∈ t
        · by_cases ht'' : 0 ∈ t
          · use s₁ᶜ
            constructor
            · exact IsClosed.isOpen_compl
            · constructor
              · by_contra h₁
                have h₂ : x ∈ s₁ := by exact not_mem_compl_iff.mp h₁
                have h₃ : a x = 1 := by exact (Ne.dite_eq_left_iff fun h a ↦ h₁ h).mpr h₂
                rw [h₃] at hxt
                contradiction
              · have h₁ : s₁ᶜ ∩ U = t₁ := by {
                  unfold U
                  rw [Set.inter_union_distrib_left, Set.compl_inter_self, Set.empty_union, ← Set.diff_eq_compl_inter]
                  apply Disjoint.symm at hs₁t₁'
                  exact Disjoint.sdiff_eq_left hs₁t₁'
                }
                have h₂ : preimage a t = s₁ᶜ := by {
                  ext x'
                  simp
                  · constructor
                    · intro hx'
                      have h₁ : ¬ a x' = 1 := by {
                        by_contra h
                        rw [h] at hx'
                        contradiction
                      }
                      by_contra h
                      have h' : a x' = 1 := by exact (Ne.dite_eq_left_iff fun h_1 a ↦ h_1 h).mpr h
                      contradiction
                    · intro hx'
                      have h : a x' = 0 := by exact (Ne.dite_eq_right_iff fun h a ↦ hx' h).mpr hx'
                      rw [h]
                      exact ht''
                }
                rw [h₁, h₂]
                exact Disjoint.subset_compl_left hs₁t₁'
          · by_cases h : x ∈ s₁
            · have h₁ : a x = 1 := by exact (Ne.dite_eq_left_iff fun h_1 a ↦ h_1 h).mpr h
              rw [h₁] at hxt
              contradiction
            · have h₁ : a x = 0 := by exact (Ne.dite_eq_right_iff fun h_1 a ↦ h h_1).mpr h
              rw [h₁] at hxt
              contradiction
        · simp at ht'
          by_cases ht'' : 0 ∈ t
          · use univ
            constructor
            · exact isOpen_univ
            · constructor
              · trivial
              · have h₁ : preimage a t = univ := by {
                  ext x'
                  constructor
                  · intro hx'
                    trivial
                  · intro hx'
                    simp
                    by_cases h : x' ∈ s₁
                    · have h₁ : a x' = 1 := by exact (Ne.dite_eq_left_iff fun h_1 a ↦ h_1 h).mpr h
                      rw [h₁]
                      exact ht'
                    · have h₁ : a x' = 0 := by exact (Ne.dite_eq_right_iff fun h_1 a ↦ h h_1).mpr h
                      rw [h₁]
                      exact ht''
                }
                rw [h₁]
                exact fun ⦃a⦄ a ↦ trivial
          · use t₁ᶜ
            constructor
            · exact IsClosed.isOpen_compl
            · constructor
              · have h₁ : s₁ ⊆ t₁ᶜ := by exact Disjoint.subset_compl_left (id (Disjoint.symm hs₁t₁'))
                by_cases h : x ∈ s₁
                · exact h₁ h
                · have h₂ : a x = 0 := by exact (Ne.dite_eq_right_iff fun h_1 a ↦ h h_1).mpr h
                  rw [h₂] at hxt
                  contradiction
              · have h₁ : t₁ᶜ ∩ U = s₁ := by {
                  unfold U
                  rw [Set.inter_union_distrib_left, Set.compl_inter_self, Set.union_empty, ← Set.diff_eq_compl_inter]
                  exact Disjoint.sdiff_eq_left hs₁t₁'
                }
                have h₂ : preimage a t = s₁ := by {
                  ext x'
                  simp
                  constructor
                  · intro hx'
                    by_cases h : x' ∈ s₁
                    · exact h
                    · have h₂ : a x' = 0 := by exact (Ne.dite_eq_right_iff fun h_1 a ↦ h h_1).mpr h
                      rw [h₂] at hx'
                      contradiction
                  · intro hx'
                    have h₃ : a x' = 1 := by exact (Ne.dite_eq_left_iff fun h a ↦ h hx').mpr hx'
                    rw [h₃]
                    exact ht'
                }
                rw [h₁, h₂]
    }
    have ha' : ∃ a' : ContinuousMap X ℝ, EqOn a a' U := by exact TietzeExtension_restricts_eqOn U hs₁t₁ a ha
    obtain ⟨ a', ha' ⟩ := ha'
    by_cases hA : Nonempty A
    · sorry
    · sorry

  }

lemma adjunction_path_connected_if_comps_path_connected {X Y A : Type*}
[TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A]
(f₁ : ContinuousMap A X) {f₂ : ContinuousMap A Y} (hf₂ : Embedding f₂)
(hA : Nonempty A) (hX : PathConnectedSpace X) (hY : PathConnectedSpace Y) :
PathConnectedSpace (AdjunctionSpace f₁ hf₂) where
  nonempty := by {
    rw [← exists_true_iff_nonempty]
    rw [← exists_true_iff_nonempty] at hA
    obtain ⟨ a, ha ⟩ := hA
    let x := @Sum.inl X Y (f₁ a)
    use Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) x
  }
  joined := by {
    unfold Joined;
    intro x y
    rw [← exists_true_iff_nonempty]
    by_cases hx : ∃ x₁ : X, (pushout_map_left f₁ hf₂) x₁ = x
    · obtain ⟨ x₁, hx₁ ⟩ := hx
      by_cases hy : ∃ y₁ : X, (pushout_map_left f₁ hf₂) y₁ = y
      · obtain ⟨ y₁, hy₁ ⟩ := hy
        have hx₁y₁ : Joined x₁ y₁ := by exact PathConnectedSpace.joined x₁ y₁
        unfold Joined at hx₁y₁
        rw [← exists_true_iff_nonempty] at hx₁y₁
        obtain ⟨ p₁, hp₁ ⟩ := hx₁y₁
        let p : Path x y := {
          toFun := (pushout_map_left f₁ hf₂) ∘ p₁.toFun
          continuous_toFun := by {
            apply Continuous.comp
            · exact ContinuousMap.continuous (pushout_map_left f₁ hf₂)
            · exact p₁.continuous_toFun
          }
          source' := by simp; exact hx₁
          target' := by simp; exact hy₁
        }
        use p
      · have hy' : ∃ y₂ : Y, (pushout_map_right f₁ hf₂) y₂ = y := by {
          have h₁ : Surjective (Quotient.mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2))) := by exact surjective_quotient_mk' (s := equivalence_of_images f₁ (by apply (embedding_iff f₂).1 at hf₂; exact hf₂.2)) (X ⊕ Y)
          unfold Surjective at h₁
          specialize h₁ y
          apply Sum.exists.1 at h₁
          unfold pushout_map_left at hy; simp at hy
          obtain h_inl | h_inr := h₁
          · obtain ⟨ y_left, hy_left ⟩ := h_inl
            specialize hy y_left
            contradiction
          · unfold pushout_map_right
            simp
            exact h_inr
        }
        obtain ⟨ y₂, hy₂ ⟩ := hy'
        rw [← exists_true_iff_nonempty] at hA
        obtain ⟨ a, ha ⟩ := hA
        let a₁ := f₁ a
        let a₂ := f₂ a
        have hx₁a₁ : Joined x₁ a₁ := by exact PathConnectedSpace.joined x₁ a₁
        have ha₂y₂ : Joined a₂ y₂ := by exact PathConnectedSpace.joined a₂ y₂
        unfold Joined at hx₁a₁
        unfold Joined at ha₂y₂
        rw [← exists_true_iff_nonempty] at hx₁a₁
        rw [← exists_true_iff_nonempty] at ha₂y₂
        obtain ⟨ p₁, hp₁ ⟩ := hx₁a₁
        obtain ⟨ p₂, hp₂ ⟩ := ha₂y₂
        let p : Path x y := {
          toFun := fun x' ↦ if h : (x' : ℝ) ≤ (1 : ℝ) / (2 : ℝ) then (pushout_map_left f₁ hf₂) (p₁.toFun ⟨((2 * x') : ℝ), by {
            have h₁ : 0 ≤ (x' : ℝ) := by unfold unitInterval at x'; exact unitInterval.nonneg x'
            have h₂ : 0 ≤ 2 * (x' : ℝ) := by linarith
            have h₃ : 2 * (x' : ℝ) ≤ 1 := by linarith
            have h₄ : 0 ≤ 2 * (x' : ℝ) ∧ 2 * (x' : ℝ) ≤ 1 := by exact ⟨h₂, h₃⟩
            exact h₄
          }⟩) else (pushout_map_right f₁ hf₂) (p₂.toFun ⟨((2 * x' - 1) : ℝ), by {
            have h₁ : (x' : ℝ) ≥ (1 : ℝ) / (2 : ℝ) := by exact le_of_not_ge h
            have h₂ : 2 * (x' : ℝ) - 1 ≥ 0 := by linarith
            have h₃ : (x' : ℝ) ≤ 1 := by exact unitInterval.le_one x'
            have h₄ : 2 * (x' : ℝ) - 1 ≤ 1 := by linarith
            have h₅ : 0 ≤ 2 * (x' : ℝ) - 1 ∧ 2 * (x' : ℝ) - 1 ≤ 1 := by exact ⟨h₂, h₄⟩
            exact h₅
          }⟩)
          continuous_toFun := by {
            let toFun : unitInterval → AdjunctionSpace f₁ hf₂ := fun x' ↦ if h : (x' : ℝ) ≤ (1 : ℝ) / (2 : ℝ) then (pushout_map_left f₁ hf₂) (p₁.toFun ⟨((2 * x') : ℝ), by {
            have h₁ : 0 ≤ (x' : ℝ) := by unfold unitInterval at x'; exact unitInterval.nonneg x'
            have h₂ : 0 ≤ 2 * (x' : ℝ) := by linarith
            have h₃ : 2 * (x' : ℝ) ≤ 1 := by linarith
            have h₄ : 0 ≤ 2 * (x' : ℝ) ∧ 2 * (x' : ℝ) ≤ 1 := by exact ⟨h₂, h₃⟩
            exact h₄
          }⟩) else (pushout_map_right f₁ hf₂) (p₂.toFun ⟨((2 * x' - 1) : ℝ), by {
            have h₁ : (x' : ℝ) ≥ (1 : ℝ) / (2 : ℝ) := by exact le_of_not_ge h
            have h₂ : 2 * (x' : ℝ) - 1 ≥ 0 := by linarith
            have h₃ : (x' : ℝ) ≤ 1 := by exact unitInterval.le_one x'
            have h₄ : 2 * (x' : ℝ) - 1 ≤ 1 := by linarith
            have h₅ : 0 ≤ 2 * (x' : ℝ) - 1 ∧ 2 * (x' : ℝ) - 1 ≤ 1 := by exact ⟨h₂, h₄⟩
            exact h₅
          }⟩)
            have h_1 : ContinuousAt toFun 0 := by sorry
            have h_2 : ContinuousOn toFun (Ioo 0 ⟨(1 : ℝ)/(2 : ℝ), by {
              have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
              have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
              have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
              exact h₃
            } ⟩) := by sorry
            have h_3 : ContinuousAt toFun ⟨(1 : ℝ) / (2 : ℝ), by {
              have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
              have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
              have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
              exact h₃
            }⟩ := by sorry
            have h_4 : ContinuousOn toFun (Ioo ⟨(1 : ℝ)/(2 : ℝ), by {
              have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
              have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
              have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
              exact h₃
            } ⟩ 1) := by sorry
            have h_5 : ContinuousAt toFun 1 := by sorry
            apply continuous_iff_continuousAt.2
            intro x'
            by_cases h₁ : x' = 0
            · rw [h₁]
              simp
              sorry
            · by_cases h₂ : x' < (1 : ℝ) / (2 : ℝ)
              · have h₃ : IsOpen (Ioo (0 : unitInterval) ⟨(1 : ℝ)/(2 : ℝ), by {
                  have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
                  have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
                  have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
                  exact h₃
                } ⟩) := by exact isOpen_Ioo
                have h₄ : x' > 0 := by exact unitInterval.pos_iff_ne_zero.mpr h₁
                have h₅ : 0 < x' ∧ x' < (1 : ℝ) / (2 : ℝ) := by exact ⟨h₄, h₂⟩
                have h₆ : x' ∈ Ioo (0 : unitInterval) ⟨(1 : ℝ)/(2 : ℝ), by {
                  have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
                  have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
                  have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
                  exact h₃
                } ⟩ := by exact h₅
                apply (IsOpen.continuousOn_iff h₃).1 at h_2
                apply h_2 at h₆
                sorry
              · by_cases h₃ : x' = ⟨(1 : ℝ) / (2 : ℝ), by {
                  have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
                  have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
                  have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
                  exact h₃
                } ⟩
                · rw [h₃]
                  sorry
                · by_cases h₄ : x' < 1
                  · have h₅ : x' ≥ ⟨(1 : ℝ) / (2 : ℝ), by {
                      have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
                      have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
                      have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
                      exact h₃
                    } ⟩ := by exact le_of_not_lt h₂
                    have h₆ : x' > ⟨(1 : ℝ) / (2 : ℝ), by {
                      have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
                      have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
                      have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
                      exact h₃
                    } ⟩ := by exact lt_of_le_of_ne h₅ fun a ↦ h₃ (id (Eq.symm a))
                    have h₇ : ⟨(1 : ℝ) / (2 : ℝ), by {
                      have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
                      have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
                      have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
                      exact h₃
                    } ⟩ < x' ∧ x' < 1 := by exact ⟨h₆, h₄⟩
                    have h₈ : x' ∈ Ioo ⟨(1 : ℝ) / (2 : ℝ), by {
                      have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
                      have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
                      have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
                      exact h₃
                    } ⟩ (1 : unitInterval) := by exact h₇
                    have h₉ : IsOpen (Ioo ⟨(1 : ℝ) / (2 : ℝ), by {
                      have h₁ : 0 ≤ (1 : ℝ) / (2 : ℝ) := by linarith
                      have h₂ : (1 : ℝ) / (2 : ℝ) ≤ 1 := by linarith
                      have h₃ : 0 ≤ (1 : ℝ) / (2 : ℝ) ∧ (1 : ℝ) / (2 : ℝ) ≤ 1 := by exact ⟨ h₁, h₂⟩
                      exact h₃
                    } ⟩ (1 : unitInterval)) := by exact isOpen_Ioo
                    apply (IsOpen.continuousOn_iff h₉).1 at h_4
                    apply h_4 at h₈
                    sorry
                  · have h₅ : x' ≥ 1 := by exact le_of_not_lt h₄
                    have h₆ : x' ≤ 1 := by exact unitInterval.le_one'
                    have h₇ : (x' : ℝ) ≤ 1 := by norm_cast
                    have h₈ : (x' : ℝ) ≥ 1 := by norm_cast
                    have h₉ : (x' : ℝ) = 1 := by linarith
                    have h₁₀ : x' = 1 := by exact Eq.symm (SetCoe.ext (id (Eq.symm h₉)))
                    rw [h₁₀]
                    sorry
          }
          source' := by simp; exact hx₁
          target' := by {
            simp
            have h₁ : (1 : ℝ) > 2⁻¹ := by exact two_inv_lt_one
            have h₂ : ¬ (1 : ℝ) ≤ 2⁻¹ := by exact not_le_of_lt h₁
            refine dite_eq_iff.mpr ?_
            right
            use h₂
            norm_num
            exact hy₂
          }
        }
        use p
    · sorry
  }
