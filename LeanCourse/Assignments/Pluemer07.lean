import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Nat.Choose.Dvd
noncomputable section
open Function Ideal Polynomial Classical
open scoped Matrix
-- This is removed intentionally and should not be used manually in the exercises
attribute [-ext] LinearMap.prod_ext


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 8.2 and 9.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 26.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-
/-! # Exercises to practice.
Feel free to skip these exercises-/

example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by {
  rw [← Ideal.span_union]
  simp
  rw [@span_gcd]
  rw [@span_pair_comm]
  }

example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by {
  ext x
  constructor
  · intro hx
    rw [@mem_inf] at hx
    obtain ⟨ hx₁, hx₂⟩ := hx
    rw [@mem_span_singleton]
    rw [@lcm_dvd_iff]
    rw [@mem_span_singleton] at hx₁
    rw [@mem_span_singleton] at hx₂
    exact ⟨hx₁, hx₂⟩
  · intro hx
    rw [@mem_span_singleton] at hx
    rw [@lcm_dvd_iff] at hx
    rw [@mem_inf]
    repeat rw[@mem_span_singleton]
    exact hx
  }

/- Show that transposing a matrix gives rise to a linear equivalence. -/
example {R M m n : Type*} [Ring R] [AddCommGroup M] [Module R M] :
  Matrix m n M ≃ₗ[R] Matrix n m M where
    toFun := fun M ↦ Mᵀ
    map_add' := by exact fun x y ↦ rfl
    map_smul' := by exact fun m_1 x ↦ rfl
    invFun := fun M ↦ Mᵀ
    left_inv := by exact congrFun rfl
    right_inv := by exact congrFun rfl

/- A ring has characteristic `p` if `1 + ⋯ + 1 = 0`, where we add `1` `p` times to itself.
This is written `CharP` in Lean.
In a module over a ring with characteristic 2, for every element `m` we have `m + m = 0`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [CharP R 2] (m : M) :
    m + m = 0 := by {
      calc
      m + m = (1 : R) • m + (1 : R) • m := by rw [one_smul]
      _ = ((1 : R) + (1 : R)) • m := by rw [@add_smul]
      _= (0 : R) • m := by rw [@CharTwo.add_self_eq_zero]
      _= 0 := by exact zero_smul R m
  }

section Frobenius
variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
/- Let's define the Frobenius morphism `x ↦ x ^ p`.
You can use lemmas from the library.
We state that `p` is prime using `Fact p.Prime`.
This allows type-class inference to see that this is true.
You can access the fact that `p` is prime using `hp.out`. -/

def frobeniusMorphism (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] :
  R →+* R where
    toFun := fun x ↦ x ^ p
    map_one' := by simp
    map_mul' := by exact fun x y ↦ mul_pow x y p
    map_zero' := by {
      simp
      by_cases hp' : p = 0
      · have hp'' : Nat.Prime p := by exact hp.out
        rw [hp'] at hp''
        contradiction
      · exact zero_pow hp'
    }
    map_add' := by {
      simp
      exact fun x y ↦ add_pow_char R x y
    }

@[simp] lemma frobeniusMorphism_def (x : R) : frobeniusMorphism p R x = x ^ p := by rfl

/- Prove the following equality for iterating the frobenius morphism. -/
lemma iterate_frobeniusMorphism (n : ℕ) (x : R) : (frobeniusMorphism p R)^[n] x = x ^ p ^ n := by {
  induction n with
  | zero => simp
  | succ n ih => {
    rw [pow_add]
    simp
    rw [pow_mul]
    rw [← ih]
  }
  }

/- Show that the Frobenius morphism is injective on a domain. -/
lemma frobeniusMorphism_injective [IsDomain R] :
    Function.Injective (frobeniusMorphism p R) := by {
    unfold Injective
    intro a₁ a₂ ha₁a₂
    simp at ha₁a₂
    have h₁ : (a₁ - a₂)^p^1 = a₁^p^1 - a₂^p^1 := by exact sub_pow_char_pow R a₁ a₂
    simp at h₁
    rw [ha₁a₂] at h₁
    have h₂ : (a₁ - a₂)^p = 0 := by {
      calc
      (a₁ - a₂)^p = a₂^p - a₂^p := by exact h₁
      _= 0 := by ring
    }
    have h₃ : a₁ - a₂ = 0 := by exact pow_eq_zero h₂
    calc
    a₁ = a₁ - a₂ + a₂ := by ring
    _= 0 + a₂ := by rw [h₃]
    _= a₂ := by ring
    }

/- Show that the Frobenius morphism is bijective on a finite domain. -/
lemma frobeniusMorphism_bijective [IsDomain R] [Finite R] :
    Function.Bijective (frobeniusMorphism p R) := by {
    have h₁ : Function.Bijective (frobeniusMorphism p R) ↔ Function.Injective (frobeniusMorphism p R) := by exact Iff.symm Finite.injective_iff_bijective
    apply h₁.2
    exact frobeniusMorphism_injective p R
  }

example [IsDomain R] [Finite R] (k : ℕ) (x : R) : x ^ p ^ k = 1 ↔ x = 1 := by {
  constructor
  · intro h
    have h₁ : x ^ p ^ k = 1 ^ p ^ k := by rw [h]; rw [@one_pow]
    have h₂ : x ^ p ^ k - 1 ^ p ^ k = 0 := by rw [h]; ring
    have h₃ : (x - 1)^p^k = x^p^k - 1 ^ p ^k := by exact sub_pow_char_pow R x 1
    rw [← h₃] at h₂
    have h₄ : x - 1 = 0 := by exact pow_eq_zero h₂
    calc
    x = x - 1 + 1 := by ring
    _ = 0 + 1 := by rw [h₄]
    _ = 1 := by ring
  · intro h
    rw [h]
    exact one_pow (p ^ k)
  }

example {R : Type*} [CommRing R] [IsDomain R] [Finite R] [CharP R 2] (x : R) : IsSquare x := by {
  have h₁ : Function.Bijective (frobeniusMorphism 2 R) := by exact frobeniusMorphism_bijective 2 R
  have h₂ : Function.Surjective (frobeniusMorphism 2 R) := by exact Bijective.surjective h₁
  unfold Function.Surjective at h₂
  specialize h₂ x
  simp at h₂
  obtain ⟨ a, ha⟩ := h₂
  unfold IsSquare
  use a
  rw [@sq] at ha
  exact id (Eq.symm ha)
  }

end Frobenius


section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
prove that the units of a ring form a group.
Hint: I recommend that you first prove that the product of two units is again a unit,
and that you define the inverse of a unit separately using `Exists.choose`.
Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
(`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

def IsAUnit.mul {x y : R} (hx : IsAUnit x) (hy : IsAUnit y) : IsAUnit (x * y) := by {
  unfold IsAUnit at hx hy
  obtain ⟨ x', hx'⟩ := hx
  obtain ⟨ y', hy'⟩ := hy
  use (y' * x')
  rw [mul_assoc]
  nth_rewrite 2 [← mul_assoc]
  rw [hx']
  ring
  exact hy'
  }

instance groupUnits : Group {x : R // IsAUnit x} where
  mul := fun x ↦ (fun y ↦ ⟨ x * x, IsAUnit.mul (sorry) (sorry)⟩)
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  inv_mul_cancel := sorry

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by sorry

end Ring


-/
/-! # Exercises to hand-in. -/

/- The Frobenius morphism in a domain of characteristic `p` is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. A proof sketch is given, and the following results will be useful. -/

#check add_pow
#check CharP.cast_eq_zero_iff


variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R] [CharP R p] in
open Nat Finset in
lemma add_pow_eq_pow_add_pow (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by {
  have hp' : p.Prime := hp.out
  have range_eq_insert_Ioo : range p = insert 0 (Ioo 0 p)
  · ext x
    constructor
    · intro h
      by_cases h₁ : x = 0
      · rw [h₁]
        exact mem_insert_self 0 (Ioo 0 p)
      · have h₂ : 0 < x := by exact zero_lt_of_ne_zero h₁
        have h₃ : x < p := by exact List.mem_range.mp h
        have h₄ : 0 < x ∧ x < p := by exact ⟨h₂, h₃⟩
        have h₅ : x ∈ Ioo 0 p := by exact mem_Ioo.mpr h₄
        exact mem_insert_of_mem h₅
    · intro h
      by_cases h₁ : x = 0
      · have h₂ : x < p := by rw [h₁]; exact pos_of_neZero p
        exact mem_range.mpr h₂
      · have h₂ : x ∈ Ioo 0 p := by exact mem_of_mem_insert_of_ne h h₁
        have h₃ : 0 < x ∧ x < p := by exact (LocallyFiniteOrder.finset_mem_Ioo 0 p x).mp h₂
        have h₄ := h₃.2
        exact mem_range.mpr h₄
  have dvd_choose : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    intro i hi
    have h₁ : 0 < i ∧ i < p := by exact (LocallyFiniteOrder.finset_mem_Ioo 0 p i).mp hi
    refine Prime.dvd_choose hp' ?ha ?hab ?h
    · exact h₁.2
    · rw [@tsub_lt_self_iff]
      have h₂ := h₁.1
      have h₃ : 0 < p := by exact pos_of_neZero p
      exact ⟨h₃, h₂⟩
    · exact Nat.le_refl p
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
  calc
    _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by
      have h₁ : ∀ i ∈ Ioo 0 p, @Nat.cast R AddMonoidWithOne.toNatCast (Nat.choose p i) = 0 ↔ p ∣ Nat.choose p i := by exact fun i a ↦ CharP.cast_eq_zero_iff R p (p.choose i)
      have h₂ : ∀ i ∈ Ioo 0 p, @Nat.cast R AddMonoidWithOne.toNatCast (Nat.choose p i) = 0 := by {
        intro i hi
        have hi₁ := hi
        specialize h₁ i
        specialize dvd_choose i
        apply h₁ at hi
        apply dvd_choose at hi₁
        apply hi.2 at hi₁
        exact hi₁
      }
      have h₃ : ∀ i ∈ Ioo 0 p, x ^ i * y ^ (p - i) * @Nat.cast R AddMonoidWithOne.toNatCast (Nat.choose p i) = x ^ i * y ^ (p - i) * 0 := by {
        intro i hi
        specialize h₂ i
        apply h₂ at hi
        rw [hi]
      }
      exact sum_congr rfl h₃
    _ = 0 := by {
      simp
    }
  exact add_pow_char R x y
  }


section LinearMap

variable {R M₁ M₂ N M' : Type*} [CommRing R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup M']
  [Module R M₁] [Module R M₂] [Module R N] [Module R M']

/- Define the coproduct of two linear maps, and prove the characterization below.
Note that this proof works exactly the same for vector spaces over a field as it works
for modules over a ring, so feel free to think of `M₁`, `M₂`, `N` and `M'` as vector spaces.
You might recognize this as the characterization of a *coproduct* in category theory. -/

def coproduct (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun x := f (x.1) + g (x.2)
  map_add' x y := by {
    simp
    rw [@add_add_add_comm]
  }
  map_smul' r x := by simp

-- this can be useful to have as a simp-lemma, and should be proven by `rfl`
@[simp] lemma coproduct_def (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  coproduct f g (x, y) = f (x) + g (y) := by rfl

lemma coproduct_unique {f : M₁ →ₗ[R] N} {g : M₂ →ₗ[R] N} {l : M₁ × M₂ →ₗ[R] N} :
    l = coproduct f g ↔
    l.comp (LinearMap.inl R M₁ M₂) = f ∧
    l.comp (LinearMap.inr R M₁ M₂) = g := by {
  constructor
  · intro h
    constructor
    · ext x
      simp
      rw [h]
      simp
    · ext x
      simp
      rw [h]
      simp
  · intro h
    obtain ⟨ h₁, h₂ ⟩ := h
    ext x
    rw [coproduct_def]
    have h₃ : x = (x.1, 0) + (0, x.2) := by exact Eq.symm (Prod.fst_add_snd x)
    nth_rewrite 1 [h₃]
    have h₄ : l ((x.1,0) + (0,x.2)) = l (x.1, 0) + l (0, x.2) := by exact LinearMap.map_add l (x.1, 0) (0, x.2)
    rw [h₄]
    rw [← h₁]
    rw [← h₂]
    simp
  }


end LinearMap
