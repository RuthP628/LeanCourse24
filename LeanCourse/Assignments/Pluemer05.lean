import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical

/-! # Exercises to hand-in. -/

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

structure StrictBipointedType where
  α : Type*
  x₀ : α
  x₁ : α
  neq : x₀ ≠ x₁

lemma myLemma (s : StrictBipointedType) (z : s.α) : z ≠ s.x₀ ∨ z ≠ s.x₁ := by
  by_cases h : z = s.x₀
  · right
    rw [h]
    exact s.neq
  · left
    exact h


/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by {
  have gauss : ∀ (m : ℕ), (∑ i in range (m + 1), (i : ℚ) = m * (m + 1) / 2) := by{
    intro m
    induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring
  }
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rw [gauss]
    rw [gauss (n+1)]
    field_simp
    ring
  }

/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min -- this hypothesis allows you to use well-orderedness
  constructor
  · sorry
  · sorry
    }



/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  constructor
  · intro h
    unfold Nat.Prime at h
    have h': ¬ (∀ a b : ℕ, n ∣ a * b → n ∣ a ∨ n ∣ b) := by sorry
    have h'' : ¬ (n ≥ 2 ∧ (∀ a : ℕ, a ∣ n ↔ a = 1 ∨ a = n)) := by sorry
    /-How the hell is Nat.Prime defined? If I hover over it, it says
    `Nat.Prime p means that p is a Prime number, that is, a natural number at least two whose only divisors are p and 1`,
    but if I try defining a new hypothesis h' by replacing Nat.Prime by this definition in mathematical symbols, I can't close it with any standard method.
    On the other hand, if I unfold Nat.Prime at h, I get `¬ Irreducible n`. But if I try emulating the definition of irreducibility in rings in mathematical symbols as a new assumption h'',
    I can't close the goal with any standard method either.-/
    sorry
  · sorry
  }

lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · norm_num at hn
  · norm_num at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by {
          have h₁ : (2 : ℤ)^(a * b) = ((2 : ℤ)^a)^b := by exact pow_mul 2 a b
          exact congrFun (congrArg HMod.hMod (congrFun (congrArg HSub.hSub h₁) 1)) (2 ^ a - 1)
        }
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by {
        have h₁ : (2 : ℤ)^a ≡ 1 [ZMOD (2:ℤ)^a - 1] := by exact Int.modEq_sub (2 ^ a) 1
        have h₂ : ((2 : ℤ)^a)^b ≡ 1^b [ZMOD (2 : ℤ)^a - 1] := by exact Int.ModEq.pow b h₁
        exact Int.ModEq.sub h₂ rfl
      }
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by {
        have h₁' : (1 : ℤ)^(b) = (1 : ℤ) := by exact one_pow b
        have h₂ : 1^b ≡ 1 [ZMOD (2 : ℤ)^a - 1] := by exact congrFun (congrArg HMod.hMod h₁') (2 ^ a - 1)
        simp
        }
  have h2 : 2 ^ 2 ≤ 2 ^ a := by refine pow_le_pow_of_le_right ?hx ha; simp
  have h3 : 1 ≤ 2 ^ a := by {
    calc
    1 ≤ 2^2 := by norm_num
    _ ≤ 2^a := by exact h2
  }
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by{
    apply tsub_lt_tsub_right_of_le h3
    have h' : b > 1 := by exact hb
    have h₁ : 2^b > 2^1 := by refine Nat.pow_lt_pow_right ?ha hb; norm_num
    have h₂ : (2^b)^a > (2^1)^a := by refine Nat.pow_lt_pow_left h₁ ?_; exact not_eq_zero_of_lt ha
    calc
    2 ^ a < (2 ^ b) ^a := by exact h₂
    _ = 2^(b * a) := by exact Eq.symm (Nat.pow_mul 2 b a)
    _ = 2^(a * b) := by rw [mul_comm]
  }
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by {
    have h5' : 2^a < 2 ^(a * b) := by exact (Nat.sub_lt_sub_iff_right h3).mp h5
    have h' : 2^0 ≤ 2^a := by exact h3
    have h'' : 2^a ≤ 2^(a * b) := by exact le_of_succ_le h5'
    exact le_trans h3 h''
  }
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by norm_cast at h
  rw [Nat.prime_def_lt] at hn
  obtain ⟨ hn₁, hn₂ ⟩ := hn
  specialize hn₂ (2^a - 1)
  apply hn₂ at h5
  have h' : 2^a - 1 ∣ 2^(a * b) - 1 := by exact h'
  apply hn₂ at h'
  apply h4
  exact h'
  exact False.elim (h4 (h5 h'))
  }

/- Prove that for positive `a` and `b`, `a^2 + b` and `b^2 + a` cannot both be squares.
Prove it on paper first! -/
lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
  by_contra h
  push_neg at h
  obtain ⟨ h₁, h₂⟩ := h
  unfold IsSquare at h₁ h₂
  obtain ⟨ x, hx ⟩ := h₁
  obtain ⟨ y, hy ⟩ := h₂
  let a' := ((x : ℤ) - a)
  let b' := (y : ℤ) - b
  have h1 : a + a' = x := by {
    calc
    a + a' = a + ((x : ℤ) - (a : ℤ)) := by rfl
    _ = a + (x : ℤ) - (a : ℤ) := by rw [Int.add_sub_assoc]
    _ = a - (a : ℤ) + (x : ℤ) := by rw [@add_sub_right_comm]
    _ = 0 + (x : ℤ) := by rw [Int.sub_eq_zero_of_eq rfl]
    _ = (x : ℤ) := by exact Int.zero_add ↑x
  }
  have h2 : b + b' = y := by{
    calc
    b + b' = b + ((y : ℤ) - (b : ℤ)) := by rfl
    _ = b + (y : ℤ) - (b : ℤ) := by rw [Int.add_sub_assoc]
    _ = b - (b : ℤ) + (y : ℤ) := by rw [@add_sub_right_comm]
    _ = 0 + (y : ℤ) := by rw [Int.sub_eq_zero_of_eq rfl]
    _ = (y : ℤ) := by exact Int.zero_add ↑y
  }
  sorry
  }



/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

def groupPosReal : Group PosReal where
  inv := sorry
  inv_mul_cancel := sorry



/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] card_powerset
#check Finset.induction

lemma fintype_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (powerset s) = 2 ^ Finset.card s := by {
  induction s using Finset.induction with
  | empty => simp
  | @insert x s hxs ih =>
    rw [Finset.powerset_insert]
    have h₁ : s.powerset ∩ Finset.image (insert x) s.powerset = ∅ := by sorry
    sorry
  }
