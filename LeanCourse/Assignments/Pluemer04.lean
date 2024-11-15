import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/-! # Exercises to hand-in. -/


/- ## Converging sequences

Prove two more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma sequentialLimit_reindex {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
    unfold SequentialLimit
    unfold SequentialLimit at hs
    intro ε hε
    specialize hs ε
    apply hs at hε
    obtain ⟨ N₁, hN₁ ⟩ := hε
    specialize hr N₁
    obtain ⟨ N₂, hN₂ ⟩ := hr
    use N₂
    intro n hn
    specialize hN₂ n
    apply hN₂ at hn
    specialize hN₁ (r n)
    apply hN₁ at hn
    exact hn
  }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
  unfold SequentialLimit at hs₁ hs₃
  unfold SequentialLimit
  intro ε hε
  have hs₁' : ∃ N, ∀ n ≥ N,|s₁ n - a| < ε := by apply hs₁ at hε; exact hε
  have hs₃' : ∃ N, ∀ n ≥ N,|s₃ n - a| < ε := by apply hs₃ at hε; exact hε
  obtain ⟨ N₁, hN₁ ⟩ := hs₁'
  obtain ⟨ N₂, hN₂ ⟩ := hs₃'
  let N₃ := max N₁ N₂
  have hN₃1 : N₃ ≥ N₁ := by exact le_max_left N₁ N₂
  have hN₃2 : N₃ ≥ N₂ := by exact le_max_right N₁ N₂
  use N₃
  intro n Hn
  have hnN₁ : n ≥ N₁ := by exact le_trans hN₃1 Hn
  have hnN₂ : n ≥ N₂ := by exact le_trans hN₃2 Hn
  apply hN₁ at hnN₁
  apply hN₂ at hnN₂
  simp [abs_lt]
  constructor
  · have hs₁' : -ε < s₁ n - a := by exact neg_lt_of_abs_lt hnN₁
    have hs₁'' : -ε + a < s₁ n := by exact lt_tsub_iff_right.mp hs₁'
    specialize hs₁s₂ n
    have hs₂ : -ε + a < s₂ n := by exact gt_of_ge_of_gt hs₁s₂ hs₁''
    exact lt_add_of_neg_add_lt hs₂
  · have hs₃' : s₃ n - a < ε := by exact lt_of_abs_lt hnN₂
    have hs₁'' : s₃ n < ε + a := by exact lt_add_of_tsub_lt_right hs₃'
    specialize hs₂s₃ n
    have hs₂ : s₂ n < ε + a := by exact lt_of_le_of_lt hs₂s₃ hs₁''
    exact sub_right_lt_of_lt_add hs₂
  }

/- ## Sets -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
    ext x
    constructor
    · intro h
      obtain ⟨ hx1, hx2 ⟩ := h
      have hx3 : ∃ y ∈ s, f y = x := by exact hx1
      obtain ⟨ y, hy1 ⟩ := hx3
      have hy2 : f y ∈ t := by rw [hy1.2]; exact hx2
      have hy3 : y ∈ f⁻¹' t := by exact hy2
      have hy4 : y ∈ (s ∩ f⁻¹' t) := by {
        constructor
        · exact hy1.1
        · exact hy3
      }
      use y
      constructor
      · exact hy4
      · exact hy1.2
    · intro h
      obtain ⟨ y, hy ⟩ := h
      have hx : x ∈ t := by rw [← hy.2]; exact hy.1.2
      constructor
      · use y
        constructor
        · exact hy.1.1
        · exact hy.2
      · exact hx
  }

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
  ext x
  constructor
  · intro h
    have h1 : x^2 ≥ 16 := by exact h
    by_cases h' : x ≥ 0
    · have h2 : x ≥ √16 := by exact (sqrt_le_left h').mpr h
      have h3 : √16 = 4 := by {
        refine sqrt_eq_cases.mpr ?_
        norm_num
      }
      have h4 : x ≥ 4 := by exact le_of_eq_of_le (id (Eq.symm h3)) h2
      right
      exact h4
    · have h2 : x < 0 := by exact lt_of_not_ge h'
      have h3 : -x > 0 := by exact Left.neg_pos_iff.mpr h2
      have h4 : -x ≥ 0 := by exact le_of_lt h3
      have h5 : (-x)^2 = x^2 := by exact neg_pow_two x
      have h6 : (-x)^2 ≥ 16 := by rw [h5]; exact h1
      have h7 : -x ≥ √16 := by exact (sqrt_le_left h4).mpr h6
      have h8 : √16 = 4 := by {
        refine sqrt_eq_cases.mpr ?_
        norm_num
      }
      have h9 : -x ≥ 4 := by exact le_of_eq_of_le (id (Eq.symm h8)) h7
      have h10 : x ≤ -4 := by exact le_neg_of_le_neg h9
      left
      exact h10
  · intro h
    obtain h1|h2 := h
    · simp at h1
      have h3 : x^2 ≥ (-4)^2 := by {
        refine sq_le_sq.mpr ?_
        refine abs_le_abs_of_nonpos ?ha h1
        norm_num
      }
      have h4 : x^2 ≥ 16 := by {
        calc
        x^2 ≥ (-4)^2 := by exact h3
        _ = 16 := by rw [@neg_sq]; norm_num
      }
      simp
      exact h4
    · simp at h2
      have h3 : x^2 ≥ 4^2 := by {
        refine sq_le_sq.mpr ?_
        refine abs_le_abs h2 ?h₁
        calc
        -4 ≤ 4 := by norm_num
        _≤ x := by exact h2
      }
      have h4 : x^2 ≥ 16 := by {
        calc
        x^2 ≥ 4^2 := by exact h3
        _= 16 := by norm_num
      }
      simp
      exact h4
  }


/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
  unfold InjOn at hf
  unfold LeftInvOn
  let g : β → α := fun y ↦
    if h' : ∃ x : α, x ∈ s ∧ f x = y then
      Classical.choose h' else default
  use g
  intro x h
  simp [g]
  apply hf
  · have h' : ∃ x_1 ∈ s, f x_1 = f x := by use x
    have h'' : (if h' : ∃ x_1 ∈ s, f x_1 = f x then Classical.choose h' else default) = Classical.choose h' := by exact dif_pos h'
    rw [h'']
    simp [Classical.choose_spec h']
  · exact h
  · have h' : ∃ x_1 ∈ s, f x_1 = f x := by use x
    have h'' : (if h' : ∃ x_1 ∈ s, f x_1 = f x then Classical.choose h' else default) = Classical.choose h' := by exact dif_pos h'
    rw [h'']
    simp [Classical.choose_spec h']
}



/- Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

To help you along the way, some potentially useful ways to reformulate the hypothesis are given. -/

-- This lemma might be useful.
#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
  -- h1' and h1'' might be useful later as arguments of `simp` to simplify your goal.
  have h1' : ∀ x y, f x ≠ g y := by {
    intro x y
    by_contra h
    have h1f : f x ∈  range f := by exact mem_range_self x
    have h1g : g y ∈ range g := by exact mem_range_self y
    have h1f' : f x ∈ range g := by rw [← h] at h1g; exact h1g
    have h1f'' : f x ∈ range f ∩ range g := by exact mem_inter h1f h1f'
    simp [h1] at h1f''
  }
  have h1'' : ∀ y x, g y ≠ f x := by exact fun y x a ↦ h1' x y (id (Eq.symm a))
  have h2' : ∀ x, x ∈ range f ∪ range g := by {
    intro x
    simp [h2]
  }
  let L : Set α × Set β → Set γ := fun (a, b) ↦ image f a ∪ image g b
  let R : Set γ → Set α × Set β := fun x ↦ ({a | f a ∈ x}, {b | g b ∈ x})
  use L, R
  constructor
  · ext s x
    simp
    constructor
    · intro h
      have h₁ : x ∈ (image f (R s).1) ∪ (image g (R s).2) := by exact h
      by_cases h₂ : x ∈ image f (R s).1
      · have h₃ : ∃ y ∈ (R s).1, f y = x := by exact h₂
        obtain ⟨ y, hy ⟩ := h₃
        simp [R] at hy
        rw [← hy.2]
        exact hy.1
      · obtain h₁1 | h₁2 := h₁
        · contradiction
        · have h₃ : ∃ y ∈ (R s).2, g y = x := by exact h₁2
          obtain ⟨ y, hy ⟩ := h₃
          rw [← hy.2]
          exact hy.1
    · intro h
      by_cases h' : ∃ y, f y = x
      · obtain ⟨ y, hy ⟩ := h'
        have h₁ : f y ∈ s := by exact mem_of_eq_of_mem hy h
        have h₂ : f y ∈ image f (R s).1 := by exact mem_image_of_mem f h₁
        have h₃ : f y ∈ (image f (R s).1) ∪ (image g (R s).2) := by exact mem_union_left (g '' (R s).2) h₂
        have h₄ : f y ∈ L (R s) := by exact h₃
        rw [hy] at h₄
        exact h₄
      · have h₁ : ¬ (x ∈ range f) := by exact h'
        specialize h2' x
        obtain h2'₁ | h2'₂ := h2'
        · contradiction
        · have h₂ : ∃ y, g y = x := by exact h2'₂
          obtain ⟨ y, hy ⟩ := h₂
          have h₃ : g y ∈ s := by exact mem_of_eq_of_mem hy h
          have h₄ : g y ∈ image g (R s).2 := by exact mem_image_of_mem g h₃
          have h₅ : g y ∈ L (R s) := by exact mem_union_right (f '' {a | f a ∈ s}) h₄
          rw [hy] at h₅
          exact h₅
  · ext s x
    · simp [L]
      constructor
      · intro h
        obtain h₁ | h₂ := h
        · obtain ⟨ x₁, hx₁ ⟩ := h₁
          have h₃ : x₁ ∈ s.1 := by exact hx₁.1
          have h₄ : f x₁ = f x := by exact hx₁.2
          apply hf at h₄
          rw [h₄] at h₃
          exact h₃
        · obtain ⟨ x₁, hx₁ ⟩ := h₂
          have h₃ : g x₁ = f x := by exact hx₁.2
          specialize h1'' x₁ x
          contradiction
      · intro h
        left
        use x
    · simp
      constructor
      · intro h
        simp [L] at h
        obtain h₁ | h₂ := h
        · obtain ⟨ x₁ , hx₁ ⟩ := h₁
          specialize h1' x₁ x
          have h₃ : f x₁ = g x := by exact hx₁.2
          contradiction
        · obtain ⟨ x₁, hx₁ ⟩ := h₂
          have h₃ : g x₁ = g x := by exact hx₁.2
          apply hg at h₃
          have h₄ : x₁ ∈ s.2 := by exact hx₁.1
          rw [h₃] at h₄
          exact h₄
      · intro h
        simp [L]
        right
        use x
}
