import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real Function Set Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 2, 3, 5, 6.
  Read chapter 4, section 1.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 29.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example {p : ℝ → Prop} (h : ∀ x, p x) : ∃ x, p x := by {
  use 0
  specialize h 0
  exact h
  }


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
  intro h'
  obtain ⟨ y, hy ⟩ := h'
  apply h at hy
  use y
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by {
  constructor
  · intro h
    intro y
    intro h'
    have hx : (∃ x, p x) := by use y
    apply h at hx
    exact hx
  · intro h
    intro h'
    obtain ⟨ y, hy ⟩ := h'
    specialize h y hy
    exact h
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by {
  constructor
  · intro h
    obtain ⟨ x, hx ⟩ := h
    constructor
    · have hx' : p x := by exact hx.1
      use x
    · exact hx.2
  · intro h
    have hx : (∃ x, p x) := by exact h.1
    obtain ⟨ x, hx ⟩ := hx
    use x
    constructor
    · exact hx
    · exact h.2
  }

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  constructor
  · intro h
    intro h'
    obtain ⟨ x, hx ⟩ := h
    apply h' at hx
    exact hx
  · intro h
    by_contra h'
    apply h
    intro y
    by_cases hy : p y
    · have hy' : (∃ x, p x) := by use y
      contradiction
    · exact hy
  }

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by {
  unfold SequentialLimit
  intro ε hε
  use 0
  simp
  exact hε
  }

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/

example (n m k : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by {
  calc
  (n)! ∣ (m)! := by exact factorial_dvd_factorial h
  _ ∣ (m)! * (m+1) := by exact Nat.dvd_mul_right m ! (m+1)
  _ = (m+1) * (m)! := by rw[mul_comm]
  _ = (m+1)! := by rfl
  }

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by {
  intro h h'
  have h₁ : ∃ x ∈ f⁻¹' s, f (x) = h:= by exact h'
  obtain ⟨y, hy⟩ :=  h₁
  have h₂ : f y ∈ s := by exact hy.1
  rw [hy.2] at h₂
  exact h₂
  }

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
  intro x h₁
  unfold Surjective at h
  specialize h x
  obtain ⟨ a, ha ⟩ := h
  rw [← ha] at h₁
  have h₂ : a ∈ f⁻¹' (s) := by exact h₁
  use a
  }

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  intro x h₁
  obtain ⟨ h₂, h₃ ⟩ := h₁
  obtain ⟨ y, hy ⟩ := h₂
  obtain ⟨ z, hz ⟩ := h₃
  rw [← hz.2] at hy
  unfold Injective at h
  specialize h hy.2
  rw [h] at hy
  use z
  constructor
  · constructor
    · exact hy.1
    · exact hz.1
  · exact hz.2
  }

example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by {
  ext x
  constructor
  · intro h
    simp
    have h₁ : ∃ y ∈ ⋃ i, A i, f (y) = x := by exact h
    obtain ⟨ y, hy ⟩ := h₁
    obtain ⟨ h₂, h₃ ⟩ := hy
    simp at h₂
    obtain ⟨ i, hi ⟩ := h₂
    use i
    use y
  · intro h
    simp
    simp at h
    obtain ⟨ i, hi ⟩ := h
    obtain ⟨ x_1, h₁ ⟩ := hi
    use x_1
    constructor
    · use i
      exact h₁.1
    · exact h₁.2
  }

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by {
  ext x
  constructor
  · intro h
    simp at h
    simp
    obtain ⟨ y, hy ⟩ := h
    have h₁ : 0 ≤ y^2 := by exact sq_nonneg y
    rw [hy] at h₁
    exact h₁
  · intro h
    simp
    simp at h
    use sqrt x
    exact sq_sqrt h
    }

end Set

/-! # Exercises to hand-in. -/


/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  · intro h
    obtain ⟨ x, hx ⟩ := h
    obtain hp | hq := hx
    · left
      use x
    · right
      use x
  · intro h
    obtain h₁ | h₂ := h
    · obtain ⟨ x, hx ⟩ := h₁
      use x
      left
      exact hx
    · obtain ⟨ x, hx ⟩ := h₂
      use x
      right
      exact hx
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  constructor
  · intro h
    unfold SurjectiveFunction
    unfold SurjectiveFunction at h hf
    intro y
    specialize h y
    obtain ⟨ x, hx ⟩ := h
    simp at hx
    use f x
  · intro h
    unfold SurjectiveFunction at h hf
    unfold SurjectiveFunction
    intro y
    simp
    specialize h y
    obtain ⟨ x, hx ⟩ := h
    specialize hf x
    obtain ⟨ z, hz  ⟩ := hf
    use z
    rw [hz]
    exact hx
  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
  unfold SurjectiveFunction at hf
  unfold SurjectiveFunction
  simp
  intro y
  specialize hf ((y-1)/2)
  obtain ⟨ x, hx ⟩ := hf
  use (x/3 - 4)
  ring
  rw [hx]
  ring
  }

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  by_contra h
  unfold Surjective at h
  let R := {x | x ∉ f x}
  specialize h R
  obtain ⟨ a, ha ⟩ := h
  by_cases h₁ : (a ∈ R)
  · simp at h₁
    apply h₁
    rw [ha]
    exact h₁
  · have h₂ : a ∉ {x | x ∉ f x} := by exact h₁
    simp at h₂
    rw [ha] at h₂
    contradiction
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
  unfold SequentialLimit at hs ht
  unfold SequentialLimit
  intro ε hε
  specialize hs (ε / 2)
  specialize ht (ε / 2)
  have h₁ : ε / 2 > 0 := by exact half_pos hε
  have h₂ : ε / 2 > 0 := by exact half_pos hε
  apply hs at h₁
  apply ht at h₂
  obtain ⟨ N₁, hN₁ ⟩ := h₁
  obtain ⟨ N₂, hN₂ ⟩ := h₂
  let N := max N₁ N₂
  have h₃ : N ≥ N₁ := by exact le_max_left N₁ N₂
  have h₄ : N ≥ N₂ := by exact le_max_right N₁ N₂
  use N
  intro n hn
  have h₅ : n ≥ N₁ := by exact le_trans h₃ hn
  have h₆ : n ≥ N₂ := by exact le_trans h₄ hn
  simp
  calc
  |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring
  _≤ |s n - a| + |t n - b| := by exact abs_add_le (s n - a) (t n - b)
  _< ε / 2 + |t n - b| := by exact (add_lt_add_iff_right |t n - b|).mpr (hN₁ n h₅)
  _< ε / 2 + ε / 2 := by exact (Real.add_lt_add_iff_left (ε / 2)).mpr (hN₂ n h₆)
  _= ε := by simp
  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {
  unfold SequentialLimit at hs
  unfold SequentialLimit
  intro ε hε
  by_cases h₁ : c = 0
  · use 0
    intro n hn
    rw [h₁]
    simp
    exact hε
  · have h₂ : |c| > 0 := by exact abs_pos.mpr h₁
    have h₃ : ε / |c| > 0 := by exact div_pos hε h₂
    specialize hs (ε / |c|)
    apply hs at h₃
    obtain ⟨ N, hN ⟩ := h₃
    use N
    intro n hn
    specialize hN n
    apply hN at hn
    simp
    have h₄ : |c| ≠ 0 := by exact abs_ne_zero.mpr h₁
    have h₅ : Invertible |c| := by exact invertibleOfNonzero h₄
    calc
    |c * s n - c * a| = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ < |c| * (ε / |c|) := by exact (mul_lt_mul_left h₂).mpr hn
    _ = |c| * |c|⁻¹ * ε := by ring
    _ = ε := by simp
  }





section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by {
  unfold EventuallyGrowsFaster
  intro k
  use k
  intro n hn
  simp
  exact mul_le_mul_right (s n) hn
  }

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {
  unfold EventuallyGrowsFaster at h₁ h₂
  unfold EventuallyGrowsFaster
  intro k
  specialize h₁ k
  specialize h₂ k
  obtain ⟨ N₁, hN₁ ⟩ := h₁
  obtain ⟨ N₂, hN₂ ⟩ := h₂
  let N := max N₁ N₂
  use N
  intro n hn
  have hn₁ : n ≥ N₁ := by exact le_of_max_le_left hn
  have hn₂ : n ≥ N₂ := by exact le_of_max_le_right hn
  specialize hN₁ n
  specialize hN₂ n
  apply hN₁ at hn₁
  apply hN₂ at hn₂
  simp
  calc
  k * (t₁ n + t₂ n) = k * t₁ n + k * t₂ n := by ring
  _ ≤ s₁ n + s₂ n := by gcongr
  }

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  unfold EventuallyGrowsFaster
  use factorial
  constructor
  · intro k
    use k
    intro n hn
    simp
    calc
    k * (n)! ≤ n * (n)! := by exact mul_le_mul_right n ! hn
    _ ≤ n * (n)! + n ! := by exact le_add_right (n * n ! + 0) n !
    _ = (n + 1) * n ! := by ring
    _ = (n+1) ! := by rfl
  · exact fun n ↦ factorial_ne_zero n
  }

end Growth
