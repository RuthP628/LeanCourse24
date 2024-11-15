import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 12.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like `simp` and `rw` will not unfold definitions unless instructed to.
Tactics like `exact` and `apply` will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use `my_lemma`
  exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing `rw` to unfold the definition
  -- simp [myThree] -- works after instructing `simp` to unfold the definition
                    -- (it doesn't need `my_lemma` to then prove the goal)
  -- sorry


/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  norm_cast at h
  rw [h]
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  norm_cast
  norm_cast at h
  calc
  n + 1 < n + 3 := by simp
  _ ≤ 2 * m := by exact h
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  have h' : (n : ℚ) + 2 * m = m^2 := by exact add_eq_of_eq_sub h
  norm_cast at h'
  ring
  have h'' : 1 + n +2 * m = 1 + m^2 := by exact Mathlib.Tactic.Ring.add_pf_add_lt 1 h'
  have h''' : ((1 + n + 2 * m) : ℝ ) = ((1 + m^2) : ℝ ) := by norm_cast
  linarith
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  norm_cast
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  have h₁ : n = m * 2 := by exact Nat.eq_mul_of_div_eq_left hn h
  have h₂ : (n : ℚ) = m * 2 := by norm_cast
  linarith
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  have h' : (q : ℝ ) ≤ (q' : ℝ) := by norm_cast
  exact exp_le_exp.mpr h'
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  have h' : 0 < (n : ℝ) := by norm_cast
  exact sqrt_pos_of_pos h'
  }

/- Working with `Finset` is very similar to working with `Set`.
However, some notation, such as `f '' s` or `𝒫 s` doesn't exist for `Finset`. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  ext x
  constructor
  · intro h
    have h' : (x ∈ s ∪ t) ∧ (x ∈ t) := by exact Finset.mem_inter.mp h
    obtain ⟨ h₁, h₂ ⟩ := h'
    exact Finset.mem_union_right (s ∩ t) h₂
  · intro h
    have h' : x ∈ s ∩ t ∨ x ∈ t := by exact Finset.mem_union.mp h
    obtain h₁|h₂ := h'
    · have h₃ : x ∈ s ∧ x ∈ t := by exact Finset.mem_inter.mp h₁
      obtain ⟨ h₄, h₅ ⟩ := h₃
      have h₆ : x ∈ s ∪ t := by exact Finset.mem_union_left t h₄
      exact mem_inter_of_mem h₆ h₅
    · have h₃ : x ∈ s ∪ t := by exact Finset.mem_union_right s h₂
      exact mem_inter_of_mem h₃ h₂
  }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  constructor
  · intro h
    exact Finset.mem_image.mp h
  · intro h
    exact Finset.mem_image.mpr h
  }

/- `Disjoint` can be used to state that two (fin)sets are disjoint.
Use `Finset.disjoint_left` (or `Set.disjoint_left`) to unfold its definition.
If you have `x ∈ t \ s` apply `simp` first to get a conjunction of two conditions.
-/

#check Finset.disjoint_left

example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  simp [Finset.disjoint_left]
  intro a
  intro h₁ h₂
  exact h₁
  }


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  induction n with
  | zero => simp; rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h' : fibonacci ( 2 * n ) + fibonacci ( 2 * n + 1) = fibonacci (2 * n + 2) := by rw [fibonacci]; ring
    exact h'
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  induction n with
  | zero => simp; rw [fibonacci]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h' : fibonacci (n + 1) + fibonacci (n) = fibonacci (n+2) := by rw [fibonacci]
    have h'' : ((fibonacci (n+1)) : ℤ) + ((fibonacci (n)) : ℤ) = ((fibonacci (n+2)): ℤ) := by norm_cast
    linarith
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [left_distrib, ih]
    ring
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  induction n with
  | zero => simp; rw [fac]; rw [fac]; simp
  | succ n ih =>
    calc
    2^ (n+1) = 2^n * 2 := by rfl
    _ ≤ fac (n+1) * 2 := by exact Nat.mul_le_mul_right 2 ih
    _ ≤ fac (n+1) * n + fac (n+1) * 2 := by exact Nat.le_add_left (fac (n + 1) * 2) (fac (n + 1) * n)
    _ = fac (n+1) * (n+2) := by ring
    _ = fac (n+2) := by nth_rewrite 2 [fac]; ring
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  induction n with
  | zero => simp; rw[fac]
  | succ n ih =>
    rw [fac, ih]
    rw [mul_comm]
    rw [prod_range_succ]
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  induction n with
  | zero => simp
  | succ n ih =>
    calc
    fac (2 * (n + 1)) = fac ((2 * n + 1) + 1) := by ring
    _= fac (2 * n + 1) * (2 * n + 2) := by rw [fac]; ring
    _= fac ( 2 * n ) * (2 * n + 1) * (2 * n + 2) := by rw [fac]; ring
    _ = (fac n * 2 ^ n * ∏ i ∈ Finset.range n, (2 * i + 1)) * (2 * n + 1) * (2 * n + 2) := by rw [ih]
    _ = (fac n * 2^n * ∏ i ∈ Finset.range n, (2 * i + 1)) * (2 * n + 1) * (2 * n + 2 * 1) := by simp
    _ = (fac n * 2^n * ∏ i ∈ Finset.range n, (2 * i + 1)) * (2 * n + 1) * (2 * (n+1)) := by ring
    _ = fac n * (n+1) * 2^n * 2 * (∏ i ∈ Finset.range n, (2 * i + 1)) * (2 * n + 1) := by ring
    _ = fac (n + 1) * 2^n * 2 * (∏ i ∈ Finset.range n, (2 * i + 1)) * (2 * n + 1) := by rw [fac]; ring
    _ = fac (n + 1) * (2^n * 2) * (∏ i ∈ Finset.range n, (2 * i + 1)) * (2 * n + 1) := by ring
    _ = fac (n + 1) * 2^(n+1) * (∏ i ∈ Finset.range n, (2 * i + 1)) * (2 * n + 1) := by rfl
    _ = fac (n + 1) * 2^(n+1) * ((∏ i ∈ Finset.range n, (2 * i + 1)) * (2 * n + 1)) := by ring
    _ = fac (n + 1) * 2^(n+1) * (∏ i ∈ Finset.range (n+1), (2 * i + 1)) := by rw [prod_range_succ]
  }





/- **Exercise**.
Define scalar multiplication of a real number and a `Point`. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

def scalar (a : ℝ) (b : Point) : Point where
  x := a * b.x
  y := a * b.y
  z := a * b.z

/- **Exercise**.Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/

structure PythagoreanTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  pyth : a^2 + b^2 = c^2

def myPythagoreanTriple : PythagoreanTriple where
  a := 3
  b := 4
  c := 5
  pyth : 3^2 + 4^2 = 5^2 := by simp

def multiply (const : ℕ) (p : PythagoreanTriple) : PythagoreanTriple where
  a := const * p.a
  b := const * p.b
  c := const * p.c
  pyth : (const * p.a)^2 + (const*p.b)^2 = (const*p.c)^2 := by{
    have h' : (const * p.a)^2 + (const * p.b)^2 = const^2 * p.a^2 + const^2 * p.b^2 := by ring
    have h'' : (const * p.a)^2 + (const * p.b)^2 = const^2 * (p.a^2 + p.b^2) := by rw [h']; ring
    rw [p.pyth] at h''
    ring at h''
    ring
    exact h''
  }

/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := by {
  sorry
}



/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) := by
  sorry



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
  · unfold Pairwise
    --unfold Disjoint
    sorry
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
  inv := fun x ↦ ⟨ x⁻¹, inv_pos_of_pos x.2 ⟩
  inv_mul_cancel := by intro a; sorry



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
