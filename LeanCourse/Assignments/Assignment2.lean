import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 2, 3, 4 and 5
  Read chapter 3, sections 1, 4.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 22.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by {
  have h₂: (a = b+1) := by rw[← add_zero a, ← sub_self b, add_sub, add_comm, ← add_sub, h2]
  rw [h₂]
  rw [h₂] at h1
  rw [two_mul, add_comm, ← add_assoc] at h1
  have h₃: (b+b+b = 3) := by {
  nth_rewrite 3 [← add_zero b]
  rw[← sub_self 1]
  rw [← add_assoc, add_sub, h1]
  ring}
  have h₄: (b * 3 - 3 = 0) := by{
    ring at h₃
    rw [h₃]
    ring
  }
  nth_rewrite 2 [← one_mul 3] at h₄
  rw [← sub_mul] at h₄
  simp at h₄
  have h₅ : (b = 1) := by rw [← add_zero b, ← sub_self 1, add_sub, add_comm, ← add_sub, h₄, add_zero]
  rw [h₅]
  ring}

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by {
  repeat rw[← h1]
  ring
  }

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by {
  gcongr
  · linarith
  · linarith
  }

/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by {
  constructor
  · intro h₁
    linarith
  · intro h₂
    linarith
  }

/- Note: for purely numerical problems, you can use `norm_num`
(although `ring` or `linarith` also work in some cases). -/
example : 2 + 3 * 4 + 5 ^ 6 ≤ 7 ^ 8 := by norm_num
example (x : ℝ) : (1 + 1) * x + (7 ^ 2 - 35 + 1) = 2 * x + 15 := by norm_num

/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example (x : ℝ) (hx : x = 3) : x ^ 2 + 3 * x - 5 = 13 := by
  rw [hx]
  norm_num

example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by {
  calc
    n - m ^ 2 ≤ n - 0 := by gcongr; exact sq_nonneg m
    _= n := by ring
    _≤ n+3 := by linarith
  }

example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by {
  specialize h 2
  norm_num at h
  linarith
  }

example {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ} (h₁₂ : a₁ + a₂ + 1 ≤ b₁ + b₂) (h₃ : a₃ + 2 ≤ b₃) :
  exp (a₁ + a₂) + a₃ + 1 ≤ exp (b₁ + b₂) + b₃ + 1 := by {
    gcongr ?_ +1
    have h₆: (a₃ ≤ b₃ - 2) := by linarith
    have h₇: (rexp (a₁ + a₂) ≤ rexp (b₁ + b₂)) := by {
      norm_num
      linarith
    }
    linarith
  }


/- Divisibility also gives an order. Warning: divisibility uses a unicode character,
which can be written using `\|`. -/

/-- Prove this using calc. -/
lemma exercise_division (n m k l : ℕ) (h₁ : n ∣ m) (h₂ : m = k) (h₃ : k ∣ l) : n ∣ l := by {
  calc
  n ∣ k := by rw[h₂] at h₁; exact h₁
  _ ∣ l := by exact h₃
  }
/- We can also work with abstract partial orders. -/

section PartialOrder

variable {X : Type*} [PartialOrder X]
variable (x y z : X)

/- A partial order is defined to be an order relation `≤` with the following axioms -/
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

/- every preorder comes automatically with an associated strict order -/
example : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

/- the reverse order `≥`/`>` is defined from `≤`/`<`.
In Mathlib we usually state lemmas using `≤`/`<` instead of `≥`/`>`. -/
example : x ≥ y ↔ y ≤ x := by rfl
example : x > y ↔ y < x := by rfl


example (hxy : x ≤ y) (hyz : y ≤ z) (hzx : z ≤ x) : x = y ∧ y = z ∧ x = z := by {
  have hxz: (x ≤ z) := by apply le_trans hxy hyz
  have hyx: (y ≤ x) := by apply le_trans hyz hzx
  have hzy: (z ≤ y) := by apply le_trans hzx hxy
  constructor
  · exact le_antisymm hxy hyx
  · constructor
    · exact le_antisymm hyz hzy
    · exact le_antisymm hxz hzx
  }


end PartialOrder 


/-! # Exercises to hand-in. -/

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by {
  calc
  t^2 - 3 * t - 17 = (t-3) * t - 17 := by ring
  _≥ (10 - 3) * t - 17 := by gcongr
  _≥ (10 - 3) * 10 - 17 := by linarith
  _≥ 5 := by norm_num
  }

/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by {
  calc
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 -2 * t - 2 = (t ^ 2)^2 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 := by rw [← pow_mul t 2 2]
    _= 4^2 + 3 * t ^3 - 3 * 4 - 2 * t - 2 := by congr; rw [← add_zero (t ^ 2), ← sub_self 4, add_sub, add_comm, ← add_sub, ht]; ring; rw [← add_zero (t ^ 2), ← sub_self 4, add_sub, add_comm, ← add_sub, ht]; ring;
    _= 4^2 + (3 * t^2 - 2) * t - 3 * 4 - 2 := by ring
    _= 4^2 + (3 * 4 - 2) * t - 3 * 4 - 2 := by congr; rw [← add_zero (t ^ 2), ← sub_self 4, add_sub, add_comm, ← add_sub, ht]; ring;
    _= 10 * t + 2 := by ring
    }

/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by {
  calc
  n + 1 = 0 + n + 1 := by ring
  _≤ m ^ 2 + n + 1 := by gcongr; exact sq_nonneg m
  _ ≤ 2 + 1 := by gcongr
  _ = 3 + 0 := by ring
  _ ≤ 3 + k ^ 2 := by gcongr; exact sq_nonneg k
  }



section Min
variable (a b c : ℝ)

/- The following theorems characterize `min`.
Let's this characterization it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

lemma exercise_min_comm : min a b = min b a := by {
  have h₁ : (min a b ≤ a) := by apply min_le_left
  have h₂ : (min a b ≤ b) := by apply min_le_right
  have h₃ : (min b a ≤ a) := by apply min_le_right
  have h₄ : (min b a ≤ b) := by apply min_le_left
  have h₅ := le_min h₃ h₄
  have h₆ := le_min h₂ h₁
  exact le_antisymm h₆ h₅
  }

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by {
  have h₁ : (min a (min b c) ≤ a) := by apply min_le_left
  have h₂ : (min a (min b c) ≤ min b c) := by apply min_le_right
  have h₃ : (min (min a b) c ≤ min a b) := by apply min_le_left
  have h₄ : (min (min a b) c ≤ c) := by apply min_le_right
  have h₅ : (min a b ≤ a) := by apply min_le_left
  have h₆ : (min a b ≤ b) := by apply min_le_right
  have h₇ : (min b c ≤ b) := by apply min_le_left
  have h₈ : (min b c ≤ c) := by apply min_le_right
  have h₉ : (min a (min b c) ≤ b) := by apply le_trans h₂ h₇
  have h1 : (min a (min b c) ≤ c) := by apply le_trans h₂ h₈
  have h2 : (min (min a b) c ≤ a) := by apply le_trans h₃ h₅
  have h3 : (min (min a b) c ≤ b) := by apply le_trans h₃ h₆
  have h4 : (min (min a b) c ≤ min b c) := le_min h3 h₄
  have h5 : (min (min a b) c ≤ min a (min b c)) := le_min h2 h4
  have h6 : (min a (min b c) ≤ min a b) := le_min h₁ h₉
  have h7 : (min a (min b c) ≤ min (min a b) c) := le_min h6 h1
  exact le_antisymm h7 h5
  }

end Min

#check ne_of_lt
#check ne_of_gt

/- Prove that the following function is continuous.
You can use `Continuous.div` as the first step,
and use the search techniques to find other relevant lemmas.
`ne_of_lt`/`ne_of_gt` will be useful to prove the inequality. -/
lemma exercise_continuity : Continuous (fun x ↦ (sin (x ^ 5) * cos x) / (x ^ 2 + 1)) := by {
  apply Continuous.div
  · refine Continuous.mul ?hf.hf ?hf.hg
    · refine Continuous.comp' ?hf.hf.hg ?hf.hf.hf
      · exact continuous_sin
      · exact continuous_pow 5
    · exact continuous_cos
  refine Continuous.add ?hg.hf ?hg.hg
  · exact continuous_pow 2
  · exact continuous_const
  · have h : (∀ (x : ℝ), x^2 + 1 > 0) := by {
    intro hx;
    calc
    hx ^2 + 1 ≥ 0 + 1 := by gcongr; exact sq_nonneg hx
    _ >0 := by norm_num
    }
    intro gx
    specialize h gx
    apply ne_of_gt
    exact h
  }

/- Prove this only using `intro`/`constructor`/`obtain`/`exact` -/
lemma exercise_and_comm : ∀ (p q : Prop), p ∧ q ↔ q ∧ p := by {
  intro hp hq
  constructor
  · intro a
    obtain ⟨ a₁, a₂ ⟩ := a
    constructor
    · exact a₂
    · exact a₁
  · intro b
    obtain ⟨ b₁, b₂ ⟩ := b
    constructor
    · exact b₂
    · exact b₁
  }


/-- Prove the following properties of nondecreasing functions. -/
def Nondecreasing (f : ℝ → ℝ) : Prop := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

lemma exercise_nondecreasing_comp (f g : ℝ → ℝ) (hg : Nondecreasing g) (hf : Nondecreasing f) :
    Nondecreasing (g ∘ f) := by {
  unfold Nondecreasing at hg
  unfold Nondecreasing at hf
  unfold Nondecreasing
  unfold Function.comp
  intro x₁
  intro x₂
  intro a
  specialize hf x₁ x₂
  specialize hg (f x₁) (f x₂)
  have b : f x₁ ≤ f x₂ := hf a
  have c : g (f x₁) ≤ g (f x₂) := hg b
  exact c
  }


/-- Note: `f + g` is the function defined by `(f + g)(x) := f(x) + g(x)`.
  `simp` can simplify `(f + g) x` to `f x + g x`. -/
lemma exercise_nondecreasing_add (f g : ℝ → ℝ) (hf : Nondecreasing f) (hg : Nondecreasing g) :
    Nondecreasing (f + g) := by {
  unfold Nondecreasing at hf
  unfold Nondecreasing at hg
  unfold Nondecreasing
  intro x₁
  intro x₂
  intro a
  simp
  specialize hf x₁ x₂
  specialize hg x₁ x₂
  have b : f x₁ ≤ f x₂ := hf a
  have c : g x₁ ≤ g x₂ := hg a
  linarith
  }



/-- Prove the following property of even. -/
def EvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

lemma exercise_even_iff (f g : ℝ → ℝ) (hf : EvenFunction f) :
    EvenFunction (f + g) ↔ EvenFunction g := by {
  unfold EvenFunction at hf
  unfold EvenFunction
  constructor
  · intro a
    simp at a
    intro x₁
    specialize hf x₁
    specialize a x₁
    linarith
  · intro b
    intro x₂
    specialize b x₂
    specialize hf x₂
    simp
    linarith
  }
