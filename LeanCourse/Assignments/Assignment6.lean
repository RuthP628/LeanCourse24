import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8.1.
  Chapter 7 explains some of the design decisions for classes in Mathlib.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 19.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/
/-

/- Prove the following exercises about functions where the domain/codomain are
subtypes. -/

abbrev PosReal : Type := {x : ℝ // x > 0}

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by {
  unfold Monotone
  intro a b hab
  simp
  have h1 : ((f a) : ℝ) ≤ ((f b) : ℝ) := by exact hf hab
  have h2 : ∀ x y : ℝ, x > 0 → y > 0 → x ≤ y → log x ≤ log y := by {
    intro x y hx hy hxy
    exact (log_le_log_iff hx hy).mpr hxy
    }
  have ha : ((f a) : ℝ) > 0 := (f a).2
  have hb : ((f b) : ℝ) > 0 := (f b).2
  exact h2 (↑(f a)) (↑(f b)) ha hb (hf hab)
  }

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := by {
  unfold Monotone
  intro a b hab
  simp
  unfold Monotone at h2f
  specialize h2f hab
  have ha1 : f a ∈ Set.range f := by exact mem_range_self a
  have ha2 : f a ∈ {x | x > 0} := by exact hf ha1
  simp at ha2
  have hb1 : f b ∈ Set.range f := by exact mem_range_self b
  have hb2 : f b ∈ {x | x > 0} := by exact hf hb1
  simp at hb2
  exact (log_le_log_iff (hf ha1) (hf hb1)).mpr h2f
  }

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by {
  unfold Monotone
  intro a b hab
  simp
  have h1 : rexp a ≤ rexp b := by exact exp_le_exp.mpr hab
  exact hf h1
  }

/- Only specify that a function is well-behaved on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by {
  unfold Monotone
  intro a b hab
  simp
  have h1 : rexp a ≤ rexp b := by exact exp_le_exp.mpr hab
  have h2 : rexp a > 0 := by exact exp_pos a
  have h3 : rexp b > 0 := by exact exp_pos b
  exact hf h2 h3 h1
  }



variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup


/- State and prove that the preimage of `U` under the composition of `φ` and `ψ` is a preimage
of a preimage of `U`. This should be an equality of subgroups! -/

#check Subgroup.map
#check Subgroup.comap

example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : Subgroup.comap (ψ.comp φ) (U) = Subgroup.comap φ (Subgroup.comap ψ U)  := by {
  rfl
}

/- State and prove that the image of `S` under the composition of `φ` and `ψ`
is a image of an image of `S`. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : Subgroup.map (ψ.comp φ) S = Subgroup.map ψ (Subgroup.map φ S) := by {
  exact Eq.symm (Subgroup.map_map S ψ φ)
}



/- Define the conjugate of a subgroup, as the elements of the form `xhx⁻¹` for `h ∈ H`. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {y : G |  ∃ h : H, y = x * h * x⁻¹}
  mul_mem' := by {
    intro a b ha hb
    simp at ha hb
    simp
    obtain ⟨ h₁, hh₁ ⟩ := ha
    obtain ⟨ h₂, hh₂ ⟩ := hb
    use (h₁ * h₂)
    constructor
    · refine (Subgroup.mul_mem_cancel_right H ?h.left.h).mpr ?h.left.a
      · exact hh₂.1
      · exact hh₁.1
    · rw [hh₁.2]
      rw [hh₂.2]
      group
  }
  one_mem' := by {
    simp
    have h1 : 1 ∈ H := by exact Subgroup.one_mem H
    use 1
    constructor
    · exact h1
    · group
  }
  inv_mem' := by {
    simp
    intro g h h1 h2
    use h⁻¹
    constructor
    · exact (Subgroup.inv_mem_iff H).mpr h1
    · rw [h2]
      group
  }


/- Now let's prove that a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by {
  unfold conjugate
  simp
  rfl
  }

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by {
  unfold conjugate
  simp
  ext a
  constructor
  · intro h₁
    simp
    simp at h₁
    obtain ⟨ h, hh⟩ := h₁
    use (y * h * y⁻¹)
    constructor
    · use h
      constructor
      · exact hh.1
      · rfl
    · rw [hh.2]
      group
  · intro h₁
    obtain ⟨ g, hg⟩ := h₁
    obtain ⟨ h₂, h₃⟩ := hg
    obtain ⟨ h, hh⟩ := h₂
    rw [hh.2] at h₃
    use h
    constructor
    · exact hh.1
    · rw [h₃]
      group
  }


/- Saying that a group `G` acts on a set `X` can be done with `MulAction`.
The two examples below show the two properties that a group action must satisfy. -/
#print MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
example (g g' : G) (x : X) : (g * g') • x = g • (g' • x) := by exact?
example (x : X) : (1 : G) • x = x := by exact?

/- Now show that `conjugate` specifies a group action from `G` onto its subgroups. -/
instance : MulAction G (Subgroup G) where
  smul := fun g ↦ (fun H ↦ conjugate g H)
  one_smul := by exact conjugate_one
  mul_smul := by exact conjugate_mul

-/

/-! # Exercises to hand-in. -/


/- A `Setoid` is the name for an equivalence relation in Lean.
Let's define the smallest equivalence relation on a type `X`. -/
def myEquivalenceRelation (X : Type*) : Setoid X where
  r x y := x = y
  iseqv := {
    refl := by intro x; rfl
    symm := by intro x y hxy; exact id (Eq.symm hxy)
    trans := by intro x y z hx hy; rw [hx]; exact hy
  } -- Here you have to show that this is an equivalence.
                 -- If you click on the `sorry`, a lightbulb will appear to give the fields

/- This simp-lemma will simplify `x ≈ y` to `x = y` in the lemma below. -/
@[simp] lemma equiv_iff_eq (X : Type*) (x y : X) :
  letI := myEquivalenceRelation X; x ≈ y ↔ x = y := by rfl

/-
Now let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use `Quotient.mk` to define a map into a quotient (or its notation `⟦_⟧`)
Use `Quotient.lift` to define a map out of a quotient.
Use `Quotient.sound` to prove that two elements of the quotient are equal.
Use `Quotient.ind` to prove something for all elements of a quotient.
You can use this using the induction tactic: `induction x using Quotient.ind; rename_i x`.
-/

#check Quotient.mk
#check Quotient.lift
#check Quotient.sound
#check Quotient.ind

lemma myEquivalenceRelation_def : ∀ (a b : X), ((myEquivalenceRelation X).r a b) → a = b := by exact fun a b a ↦ a

def quotient_equiv_subtype (X : Type*) :
    Quotient (myEquivalenceRelation X) ≃ X where
      toFun := (Quotient.lift fun x ↦ x) (myEquivalenceRelation_def)
      invFun := fun x ↦ ⟦x⟧
      left_inv := by {
        unfold LeftInverse
        intro x
        induction x using Quotient.ind; rename_i x
        simp
      }
      right_inv := by {
        unfold Function.RightInverse
        unfold LeftInverse
        intro x
        simp
      }



section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below is the orbit of an element `x ∈ X` w.r.t. a group action by `G`.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by {
  constructor
  · unfold orbitOf
    intro h
    rw [h]
    simp
    use 1
    exact MulAction.one_smul y
  · unfold orbitOf
    intro h
    ext a
    constructor
    · intro h₁
      simp
      simp at h h₁
      obtain ⟨ z₁, hz₁⟩ := h
      obtain ⟨ z₂, hz₂ ⟩ := h₁
      use (z₂ * z₁⁻¹)
      rw [← hz₁]
      rw [@smul_smul]
      simp
      exact hz₂
    · intro h₁
      simp
      simp at h h₁
      obtain ⟨ z₁, hz₁ ⟩ := h
      obtain ⟨ z₂, hz₂ ⟩ := h₁
      use (z₂ * z₁)
      rw [← hz₂]
      rw [← hz₁]
      exact mul_smul z₂ z₁ x
  }

/- Define the stabilizer of an element `x` as the subgroup of elements
`g ∈ G` that satisfy `g • x = x`. -/
def stabilizerOf (x : X) : Subgroup G where
  carrier := { g | g • x = x}
  mul_mem' := by {
    intro a b ha hb
    simp at ha hb
    simp
    nth_rewrite 2 [← ha]
    nth_rewrite 2 [← hb]
    exact mul_smul a b x
  }
  one_mem' := by simp
  inv_mem' := by {
    simp
    intro y hy
    nth_rewrite 1 [← hy]
    simp
  }

-- This is a lemma that allows `simp` to simplify `x ≈ y` in the proof below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

/- Let's probe the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use `Equiv.ofBijective` to get an equivalence.
(Note that we are coercing `orbitOf G x` to a (sub)type in the right-hand side) -/

#check Equiv.ofBijective

def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x := by {
  have h1 : ∀ g₁ g₂ : G, g₁⁻¹ * g₂ ∈ stabilizerOf G x → g₁ • x = g₂ • x := by {
    intro g₁ g₂ h
    unfold stabilizerOf at h
    simp at h
    nth_rewrite 1 [← h]
    refine eq_inv_smul_iff.mp ?_
    exact mul_smul g₁⁻¹ g₂ x
  }
  let OrbitStabilizerBijection : G ⧸ stabilizerOf G x → orbitOf G x := sorry
  have h2: Bijective OrbitStabilizerBijection := by sorry
  exact Equiv.ofBijective OrbitStabilizerBijection h2
  }

/- How do I use that elements of G ⧸ stabilizerOf G x have the shape g * stabilizerOf G x?
 I want to map g * stabilizerOf G x to g ● x, but that doesn't work because I cannot obtain a g from something,
 Quotient.lift only lets me handle abstract whole elements ⟦X⟧ of G ⧸ stabilizerOf G x, I don't know how to use the definition of G ⧸ stabilizerOf G x -/

end GroupActions
