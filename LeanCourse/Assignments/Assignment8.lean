import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 10.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 3.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-
/-! # Exercises to practice. -/

/- You can use `filter_upwards` to conveniently conclude `Eventually` statements from `Eventually`
in one or more hypotheses using the same filter. -/
example {ι : Type*} {L : Filter ι} {f g : ι → ℝ} (h1 : ∀ᶠ i in L, f i ≤ g i)
    (h2 : ∀ᶠ i in L, g i ≤ f i) : ∀ᶠ i in L, f i = g i := by
  filter_upwards [h1, h2] with i h1 h2
  exact le_antisymm h1 h2

example {ι : Type*} {L : Filter ι} {a b : ι → ℤ} (h1 : ∀ᶠ i in L, a i ≤ b i + 1)
    (h2 : ∀ᶠ i in L, b i ≤ a i + 1) (h3 : ∀ᶠ i in L, b i ≠ a i) : ∀ᶠ i in L, |a i - b i| = 1 := by {
  filter_upwards [h1, h2, h3] with i h1' h2' h3'
  rw [propext (abs_eq (Int.NonNeg.mk (1 + 0)))]
  omega
  }

/- The goal of the following exercise is to prove that
the regular open sets in a topological space form a complete boolean algebra.
`U ⊔ V` is given by `interior (closure (U ∪ V))`.
`U ⊓ V` is given by `U ∩ V`. -/


variable {X : Type*} [TopologicalSpace X]

variable (X) in
structure RegularOpens where
  carrier : Set X
  isOpen : IsOpen carrier
  regular' : interior (closure carrier) = carrier

namespace RegularOpens

/- We write some lemmas so that we can easily reason about regular open sets. -/
variable {U V : RegularOpens X}

instance : SetLike (RegularOpens X) X where
  coe := RegularOpens.carrier
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ _ => by congr

theorem le_def {U V : RegularOpens X} : U ≤ V ↔ (U : Set X) ⊆ (V : Set X) := by simp
@[simp] theorem regular {U : RegularOpens X} : interior (closure (U : Set X)) = U := U.regular'

@[simp] theorem carrier_eq_coe (U : RegularOpens X) : U.1 = ↑U := rfl

@[ext] theorem ext (h : (U : Set X) = V) : U = V :=
  SetLike.coe_injective h


/- First we want a complete lattice structure on the regular open sets.
We can obtain this from a so-called `GaloisCoinsertion` with the closed sets.
This is a pair of maps
* `l : RegularOpens X → Closeds X`
* `r : Closeds X → RegularOpens X`
with the properties that
* for any `U : RegularOpens X` and `C : Closeds X` we have `l U ≤ C ↔ U ≤ r U`
* `r ∘ l = id`
If you know category theory, this is an *adjunction* between orders
(or more precisely, a coreflection).
-/

/- The closure of a regular open set. Of course mathlib knows that the closure of a set is closed.
(the `simps` attribute will automatically generate the simp-lemma for you that
`(U.cl : Set X) = closure (U : Set X)`
-/
@[simps]
def cl (U : RegularOpens X) : Closeds X :=
  ⟨closure U, {
    isOpen_compl := by simp
  }⟩

/- The interior of a closed set. You will have to prove yourself that it is regular open. -/
@[simps]
def _root_.TopologicalSpace.Closeds.int (C : Closeds X) : RegularOpens X :=
  ⟨interior C, by simp, by {
    have h : closure (interior (@SetLike.coe (Closeds X) X Closeds.instSetLike C)) = C := by {
      have h' : closure (interior (@SetLike.coe (Closeds X) X Closeds.instSetLike C)) ⊆ C := by {
        have h₂: IsClosed (@SetLike.coe (Closeds X) X Closeds.instSetLike C) := by exact Closeds.closed C
        exact IsClosed.closure_interior_subset h₂
      }
      have h'' : closure (interior (@SetLike.coe (Closeds X) X Closeds.instSetLike C)) ⊇ C := by {
        sorry
      }
      exact Eq.symm (Subset.antisymm h'' h')
    }
    exact congrArg interior h
  }⟩

/- Now let's show the relation between these two operations. -/
lemma cl_le_iff {U : RegularOpens X} {C : Closeds X} :
    U.cl ≤ C ↔ U ≤ C.int := by sorry

@[simp] lemma cl_int : U.cl.int = U := by sorry

/- This gives us a GaloisCoinsertion. -/

def gi : GaloisCoinsertion cl (fun C : Closeds X ↦ C.int) where
  gc U C := cl_le_iff
  u_l_le U := by simp
  choice C hC := C.int
  choice_eq C hC := rfl

/- It is now a general theorem that we can lift the complete lattice structure from `Closeds X`
to `RegularOpens X`. The lemmas below give the definitions of the lattice operations. -/

instance completeLattice : CompleteLattice (RegularOpens X) :=
  GaloisCoinsertion.liftCompleteLattice gi

@[simp] lemma coe_inf {U V : RegularOpens X} : ↑(U ⊓ V) = (U : Set X) ∩ V := by
  have : U ⊓ V = (U.cl ⊓ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_sup {U V : RegularOpens X} : ↑(U ⊔ V) = interior (closure ((U : Set X) ∪ V)) := by
  have : U ⊔ V = (U.cl ⊔ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_top : ((⊤ : RegularOpens X) : Set X) = univ := by
  have : (⊤ : RegularOpens X) = (⊤ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_bot : ((⊥ : RegularOpens X) : Set X) = ∅ := by
  have : (⊥ : RegularOpens X) = (⊥ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_sInf {U : Set (RegularOpens X)} :
    ((sInf U : RegularOpens X) : Set X) =
    interior (⋂₀ ((fun u : RegularOpens X ↦ closure u) '' U)) := by
  have : sInf U = (sInf (cl '' U)).int := rfl
  simp [this]

@[simp] lemma Closeds.coe_sSup {C : Set (Closeds X)} : ((sSup C : Closeds X) : Set X) =
    closure (⋃₀ ((↑) '' C)) := by
  have : sSup C = Closeds.closure (sSup ((↑) '' C)) := rfl
  simp [this]

@[simp] lemma coe_sSup {U : Set (RegularOpens X)} :
    ((sSup U : RegularOpens X) : Set X) =
    interior (closure (⋃₀ ((fun u : RegularOpens X ↦ closure u) '' U))) := by
  have : sSup U = (sSup (cl '' U)).int := rfl
  simp [this]

/- We still have to prove that this gives a distributive lattice.
Warning: these are hard. -/
instance completeDistribLattice : CompleteDistribLattice (RegularOpens X) :=
  CompleteDistribLattice.ofMinimalAxioms
  { completeLattice with
    inf_sSup_le_iSup_inf := by sorry
    iInf_sup_le_sup_sInf := by sorry
    }

/- Finally, we can show that the regular open subsets form a complete Boolean algebra.
Define `compl` and`coe_compl` holds and complete the instance below. -/

structure CompleteBooleanAlgebra.MinimalAxioms (α : Type*) extends
    CompleteDistribLattice.MinimalAxioms α, HasCompl α where
  inf_compl_le_bot : ∀ (x : α), x ⊓ xᶜ ≤ ⊥
  top_le_sup_compl : ∀ (x : α), ⊤ ≤ x ⊔ xᶜ

abbrev CompleteBooleanAlgebra.ofMinimalAxioms {α : Type*}
    (h : CompleteBooleanAlgebra.MinimalAxioms α) : CompleteBooleanAlgebra α where
      __ := h
      le_sup_inf x y z :=
        let z := CompleteDistribLattice.ofMinimalAxioms h.toMinimalAxioms
        le_sup_inf


instance : HasCompl (RegularOpens X) where
  compl U := {
    carrier := sorry
    isOpen := sorry
    regular' := sorry
  }

@[simp]
lemma coe_compl (U : RegularOpens X) : ↑Uᶜ = interior (U : Set X)ᶜ := sorry

instance completeBooleanAlgebra : CompleteBooleanAlgebra (RegularOpens X) :=
  CompleteBooleanAlgebra.ofMinimalAxioms {
    inf_sSup_le_iSup_inf := completeDistribLattice.inf_sSup_le_iSup_inf
    iInf_sup_le_sup_sInf := completeDistribLattice.iInf_sup_le_sup_sInf
    inf_compl_le_bot := by
      sorry
    top_le_sup_compl := by
      sorry
  }
-/
/-! # Exercises to hand-in. -/

/- Here is a technical property using filters, characterizing when a 2-valued function converges to
a filter of the form `if q then F else G`. The next exercise is a more concrete application.
Useful lemmas here are
* `Filter.Eventually.filter_mono`
* `Filter.Eventually.mono` -/

#check Filter.Eventually.filter_mono
#check Filter.Eventually.mono

lemma technical_filter_exercise {ι α : Type*} {p : ι → Prop} {q : Prop} {a b : α}
    {L : Filter ι} {F G : Filter α}
    (hbF : ∀ᶠ x in F, x ≠ b) (haG : ∀ᶠ x in G, x ≠ a) (haF : pure a ≤ F) (hbG : pure b ≤ G) :
    (∀ᶠ i in L, p i ↔ q) ↔
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) := by {
  have hab : a ≠ b
  · exact haF hbF
  rw [tendsto_iff_eventually]
  constructor
  · intro h
    intro p_1 hp_1
    by_cases h' : q
    · have h₁ : (if q then F else G) = F := by exact if_pos h'
      rw [h₁] at hp_1
      filter_upwards [h] with i h
      apply h.2 at h'
      have h₂ : (if p i then a else b) = a := by exact if_pos h'
      rw [h₂]
      exact haF hp_1
    · have h₁ : (if q then F else G) = G := by exact if_neg h'
      rw [h₁] at hp_1
      filter_upwards [h] with i h
      have h₂ : ¬ p i := by exact (iff_false_right h').mp h
      have h₃ : (if p i then a else b) = b := by exact if_neg h₂
      rw [h₃]
      exact hbG hp_1
  · intro h
    by_cases h₁ : q
    · have h' : (if q then F else G) = F := by exact if_pos h₁
      rw [h'] at h
      specialize h hbF
      filter_upwards [h] with i
      by_cases h'' : p i
      · have h₁'' : (if p i then a else b) = a := by exact if_pos h''
        rw [h₁'']
        intro h₂
        constructor
        · intro h₃
          exact h₁
        · intro h₃
          exact h''
      · have h₁'' : (if p i then a else b) = b := by exact if_neg h''
        rw [h₁'']
        intro h₂
        contradiction
    · have h' : (if q then F else G) = G := by exact if_neg h₁
      rw [h'] at h
      specialize h haG
      filter_upwards [h] with i
      intro h₂
      constructor
      · by_cases h₃ : p i
        · have h₄ : (if p i then a else b) = a := by exact if_pos h₃
          rw [h₄] at h₂
          contradiction
        · intro h₄
          contradiction
      · intro h₃
        contradiction
  }

/- To be more concrete, we can use the previous lemma to prove the following.
if we denote the characteristic function of `A` by `1_A`, and `f : ℝ → ℝ` is a function,
then  `f * 1_{s i}` tends to `f * 1_t` iff `x ∈ s i` is eventually equivalent to
`x ∈ t` for all `x`. (note that this does *not* necessarily mean that `s i = t` eventually).
`f * 1_t` is written `indicator t f` in Lean.
Useful lemmas for this exercise are `indicator_apply`, `apply_ite` and `tendsto_pi_nhds`. -/

#check indicator_apply
#check apply_ite
#check tendsto_pi_nhds

lemma tendsto_indicator_iff {ι : Type*} {L : Filter ι} {s : ι → Set ℝ} {t : Set ℝ} {f : ℝ → ℝ}
    (ha : ∀ x, f x ≠ 0) :
    (∀ x, ∀ᶠ i in L, x ∈ s i ↔ x ∈ t) ↔
    Tendsto (fun i ↦ indicator (s i) f) L (𝓝 (indicator t f)) := by {
  constructor
  · intro h
    rw [tendsto_iff_eventually]
    intro p_1 hp_1
    have h' : ∀ (x : ℝ), @Filter.Eventually ι (fun i ↦ (s i).indicator f x = f x ↔ t.indicator f x = f x) L := by {
      have h₁' : ∀ (x : ℝ), x ∈ t ↔ t.indicator f x = f x := by {
        intro x
        constructor
        · intro hx
          exact indicator_of_mem hx f
        · intro hx
          by_contra hx'
          have hx'' : t.indicator f x = 0 := by exact indicator_of_not_mem hx' f
          rw [hx''] at hx
          specialize ha x
          exact ha (id (Eq.symm hx))
        }
      have hx' : ∀ (x : ℝ), @Filter.Eventually ι (fun i ↦ x ∈ s i ↔ t.indicator f x = f x) L := by intro x; specialize h x; simp_all
      have h₂' : ∀ (x : ℝ), ∀ (i : ι), x ∈ s i ↔ (s i).indicator f x = f x := by {
        intro x i
        constructor
        · intro hx
          exact indicator_of_mem hx f
        · intro hx
          by_contra hx'
          have hx'' : (s i).indicator f x = 0 := by exact indicator_of_not_mem hx' f
          rw [hx''] at hx
          specialize ha x
          exact ha (id (Eq.symm hx))
      }
      intro x
      specialize h₂' x
      specialize hx' x
      filter_upwards [hx'] with i hx'
      specialize h₂' i
      exact Iff.trans (id (Iff.symm h₂')) hx'
    }
    have h'' : ∀ᶠ (i : ι) in L, sorry := by sorry -- i want to say that eventually, (s i).indicator f will be "in the set of points very close to t.indicator f", but I don't know how to state that formally
    sorry
  · intro h
    rw [tendsto_iff_eventually] at h
    intro x
    sorry
  }
  /-i didn't manage to actually apply the previous lemma because I couldn't
  figure out how to get rid of the quantification over x
  (I am aware that the p i from the previous lemma should probably be something as x ∈ s i,
  q should be something like x ∈ t, a and b should be f and the constant 0 function, respectively,
  and F and G should be something like the neighborhood filter of f and the neighbourhood filter of const 0,
  but the quantification still didn't make sense to me)-/
