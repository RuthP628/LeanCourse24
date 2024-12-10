import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
noncomputable section

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace


/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 11 & 12.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 10.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example (x : ℝ) :
    deriv (fun x ↦ Real.exp (x ^ 2)) x = 2 * x * Real.exp (x ^ 2) := by {
    simp
    rw [mul_comm]
  }

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ∞} in
/- In this exercise you should combine the right lemmas from the library,
in particular `IsBoundedBilinearMap.contDiff`. -/
example (L : E →L[𝕜] E →L[𝕜] E) (f g : E → E) (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun z : E × E ↦ L (f z.1) (g z.2)) := by {
  have hb : IsBoundedBilinearMap 𝕜 (fun z : E × E ↦ L (f z.1) (g z.2)) := by {
    sorry
  }
  exact IsBoundedBilinearMap.contDiff hb
  }

#check IsBoundedBilinearMap.contDiff
#check IsBoundedBilinearMap

section

variable (α : Type*)
 [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the exercise in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/

#check intermediate_value_uIcc
#check uIcc_of_le
#check mem_uIcc

#check ConditionallyCompleteLinearOrder α

lemma mono_exercise_part1 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  by_contra h
  have h₁ : f a > f x := by exact lt_of_not_ge h
  have h₂ : ContinuousOn f (uIcc x b) := by exact Continuous.continuousOn hf
  have h₃ : (uIcc (f x) (f b)) ⊆ image f (uIcc x b) := by exact intermediate_value_uIcc h₂
  have h₄ : f x < f b := by exact gt_trans h2ab h₁
  have h₅ : uIcc (f x) (f b) = Icc (f x) (f b) := by exact uIcc_of_lt h₄
  have h₆ : f x ≤ f a ∧ f a ≤ f b := by {
    constructor
    · exact le_of_not_ge h
    · exact le_of_lt h2ab
  }
  have h₇ : f a ∈ Icc (f x) (f b) := by exact h₆
  have h₈ : f a ∈ image f (uIcc x b) := by {
    rw [← h₅] at h₇
    exact h₃ h₇
  }
  by_cases h₉ : x ≤ b
  · have h_1 : uIcc x b = Icc x b := by exact uIcc_of_le h₉
    rw [h_1] at h₈
    have h_2 : ∃ y ∈ Icc x b, f a = f y := by {
      have h_3 : ∃ z ∈ image f (Icc x b), f a = z := by exact exists_eq_right'.mpr h₈
      obtain ⟨z, hz⟩ := h_3
      obtain ⟨hz₁, hz₂⟩ := hz
      unfold image at hz₁
      have h_2 : ∃ y ∈ Icc x b, f y = z := by exact hz₁
      obtain ⟨y, hy⟩ := h_2
      use y
      constructor
      · exact hy.1
      · rw [← hy.2] at hz₂
        exact hz₂
    }
    obtain ⟨y, hy⟩ := h_2
    unfold Injective at h2f
    specialize h2f hy.2
    obtain ⟨ hy1, hy2 ⟩ := hy
    have h_3 : x ≤ y := by simp_all
    rw [← h2f] at h_3
    have h_5 : x = a := by {
      have h1 : x < a ∨ x = a := by exact Decidable.lt_or_eq_of_le h_3
      have h2 : x > a ∨ x = a := by exact LE.le.gt_or_eq hx
      by_cases h' : x < a
      · by_cases h'' : x > a
        · have h''' : x < x := by exact gt_of_ge_of_gt hx h'
          have h'''' : x ≠ x := by exact ne_of_lt h'''
          exact False.elim (h'''' rfl)
        · obtain h2_1 | h2_2 := h2
          · contradiction
          · exact h2_2
      · obtain h1_1 | h1_2 := h1
        · contradiction
        · exact h1_2
    }
    rw [h_5] at h₁
    have h_6 : f a ≠ f a := by exact ne_of_lt h₁
    exact h_6 rfl
  · have h_1 : x > b := by exact lt_of_not_ge h₉
    have h_2 : uIcc x b = Icc b x := by exact uIcc_of_gt h_1
    rw [h_2] at h₈
    have h_3 : ∃ z ∈ image f (Icc b x), f a = z := by exact exists_eq_right'.mpr h₈
    obtain ⟨ z, hz ⟩ := h_3
    obtain ⟨ hz1, hz2 ⟩ := hz
    have h_4 : ∃ y ∈ Icc b x, f y = z := by exact hz1
    obtain ⟨y, hy⟩ := h_4
    obtain ⟨hy1, hy2⟩ := hy
    rw [← hz2] at hy2
    apply h2f at hy2
    rw [hy2] at hy1
    have h_3 : b ≤ a ∧ a ≤ x := by exact hy1
    have h_4 : a = b := by {
      obtain ⟨ h_3₁, h_3₂ ⟩ := h_3
      have h1 : a < b ∨ a = b := by exact Decidable.lt_or_eq_of_le hab
      have h2 : b < a  ∨ b = a := by exact Decidable.lt_or_eq_of_le h_3₁
      obtain h1_1 | h1_2 := h1
      · obtain h2_1 | h2_2 := h2
        · have h_4 : a < a := by exact gt_of_ge_of_gt h_3₁ h1_1
          have h_5 : a ≠ a := by exact ne_of_lt h_4
          exact False.elim (h_5 (h2f (h2f (h2f rfl))))
        · exact h2f (h2f (congrArg f (congrArg f (id (Eq.symm h2_2)))))
      · exact h2f (h2f (congrArg f (congrArg f h1_2)))
    }
    rw [h_4] at h2ab
    have h_5 : f b ≠ f b := by exact ne_of_lt h2ab
    exact h_5 (h2f (h2f (h2f rfl)))
  }

/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma mono_exercise_part2 {f : α → α} (hf : Continuous f) (h2f : Injective f)
    {a b : α} (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by {
  sorry
  }

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma mono_exercise_part3 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by {
  have : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b)
  · intro a b hab h2ab
    have := mono_exercise_part2 (OrderDual ℝ) hf h2f hab h2ab
    rw [strictMonoOn_dual_iff.symm] at this
    exact this
  sorry
  }

end

/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/

example : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by {
  intro h
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0 := by {
    sorry
    }
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0 := by {
    sorry
    }
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by {
  sorry
  }
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by {
  sorry
  }
  -- sorry
  sorry
  }



/- There are special cases of the change of variables theorems for affine transformations
(but you can also use the change of variable theorem from the lecture) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2  + 3) := by {
  sorry
  }

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by {
  sorry
  }

example (x : ℝ) : ∫ t in (0)..x, t * exp t = (x - 1) * exp x + 1 := by {
  sorry
  }

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by {
  sorry
  }


/-! # Exercises to hand-in. -/

/- This is a copy of `mono_exercise_part1` above. See the comments there for more info. -/
variable (α : Type*) [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] in
lemma mono_exercise_part1_copy {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  by_contra h
  have h₁ : f a > f x := by exact lt_of_not_ge h
  have h₂ : ContinuousOn f (uIcc x b) := by exact Continuous.continuousOn hf
  have h₃ : (uIcc (f x) (f b)) ⊆ image f (uIcc x b) := by exact intermediate_value_uIcc h₂
  have h₄ : f x < f b := by exact gt_trans h2ab h₁
  have h₅ : uIcc (f x) (f b) = Icc (f x) (f b) := by exact uIcc_of_lt h₄
  have h₆ : f x ≤ f a ∧ f a ≤ f b := by {
    constructor
    · exact le_of_not_ge h
    · exact le_of_lt h2ab
  }
  have h₇ : f a ∈ Icc (f x) (f b) := by exact h₆
  have h₈ : f a ∈ image f (uIcc x b) := by {
    rw [← h₅] at h₇
    exact h₃ h₇
  }
  by_cases h₉ : x ≤ b
  · have h_1 : uIcc x b = Icc x b := by exact uIcc_of_le h₉
    rw [h_1] at h₈
    have h_2 : ∃ y ∈ Icc x b, f a = f y := by {
      have h_3 : ∃ z ∈ image f (Icc x b), f a = z := by exact exists_eq_right'.mpr h₈
      obtain ⟨z, hz⟩ := h_3
      obtain ⟨hz₁, hz₂⟩ := hz
      unfold image at hz₁
      have h_2 : ∃ y ∈ Icc x b, f y = z := by exact hz₁
      obtain ⟨y, hy⟩ := h_2
      use y
      constructor
      · exact hy.1
      · rw [← hy.2] at hz₂
        exact hz₂
    }
    obtain ⟨y, hy⟩ := h_2
    unfold Injective at h2f
    specialize h2f hy.2
    obtain ⟨ hy1, hy2 ⟩ := hy
    have h_3 : x ≤ y := by simp_all
    rw [← h2f] at h_3
    have h_5 : x = a := by {
      have h1 : x < a ∨ x = a := by exact Decidable.lt_or_eq_of_le h_3
      have h2 : x > a ∨ x = a := by exact LE.le.gt_or_eq hx
      by_cases h' : x < a
      · by_cases h'' : x > a
        · have h''' : x < x := by exact gt_of_ge_of_gt hx h'
          have h'''' : x ≠ x := by exact ne_of_lt h'''
          exact False.elim (h'''' rfl)
        · obtain h2_1 | h2_2 := h2
          · contradiction
          · exact h2_2
      · obtain h1_1 | h1_2 := h1
        · contradiction
        · exact h1_2
    }
    rw [h_5] at h₁
    have h_6 : f a ≠ f a := by exact ne_of_lt h₁
    exact h_6 rfl
  · have h_1 : x > b := by exact lt_of_not_ge h₉
    have h_2 : uIcc x b = Icc b x := by exact uIcc_of_gt h_1
    rw [h_2] at h₈
    have h_3 : ∃ z ∈ image f (Icc b x), f a = z := by exact exists_eq_right'.mpr h₈
    obtain ⟨ z, hz ⟩ := h_3
    obtain ⟨ hz1, hz2 ⟩ := hz
    have h_4 : ∃ y ∈ Icc b x, f y = z := by exact hz1
    obtain ⟨y, hy⟩ := h_4
    obtain ⟨hy1, hy2⟩ := hy
    rw [← hz2] at hy2
    apply h2f at hy2
    rw [hy2] at hy1
    have h_3 : b ≤ a ∧ a ≤ x := by exact hy1
    have h_4 : a = b := by {
      obtain ⟨ h_3₁, h_3₂ ⟩ := h_3
      have h1 : a < b ∨ a = b := by exact Decidable.lt_or_eq_of_le hab
      have h2 : b < a  ∨ b = a := by exact Decidable.lt_or_eq_of_le h_3₁
      obtain h1_1 | h1_2 := h1
      · obtain h2_1 | h2_2 := h2
        · have h_4 : a < a := by exact gt_of_ge_of_gt h_3₁ h1_1
          have h_5 : a ≠ a := by exact ne_of_lt h_4
          exact False.elim (h_5 (h2f (h2f (h2f rfl))))
        · exact h2f (h2f (congrArg f (congrArg f (id (Eq.symm h2_2)))))
      · exact h2f (h2f (congrArg f (congrArg f h1_2)))
    }
    rw [h_4] at h2ab
    have h_5 : f b ≠ f b := by exact ne_of_lt h2ab
    exact h_5 (h2f (h2f (h2f rfl)))
  }
/- Prove the following using the change of variables theorem. -/
lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in (0)..π, sin x * f (cos x) = ∫ y in (-1)..1, f y := by {
    have h₁ : image cos (Icc 0 π) = Icc (-1) (1) := by {
      have h1 : image cos (Icc 0 π) ⊆ Icc (-1) (1) := by {
        have h_1: ∀ x ∈ Icc 0 π, cos x ∈ Icc (-1) (1) := by exact fun x a ↦ cos_mem_Icc x
        exact image_subset_iff.mpr h_1
      }
      have h2 : image cos (Icc 0 π) ⊇ Icc (-1) (1) := by {
        have h_1 : ContinuousOn cos (uIcc 0 π) := by exact continuousOn_cos
        have h_2 : uIcc (cos 0) (cos π) ⊆ image cos (uIcc 0 π) := by exact intermediate_value_uIcc h_1
        have h_3 : cos 0 = 1 := by exact cos_zero
        rw [h_3] at h_2
        have h_4 : cos π = -1 := by exact cos_pi
        rw [h_4] at h_2
        have h_6 : 0 < π := by exact pi_pos
        have h_7 : uIcc 0 π = Icc 0 π := by exact uIcc_of_lt h_6
        rw [h_7] at h_2
        calc
        image cos (Icc 0 π) ⊇ uIcc (1) (-1) := by exact h_2
        _ = Icc (-1) (1) := by {
          have h_8 : ((-1) : ℝ) < (1 : ℝ) := by norm_cast
          exact uIcc_of_gt h_8
        }
      }
      exact Eq.symm (Subset.antisymm h2 h1)
    }
    have h₂ : MeasurableSet (Icc 0 π) := by exact measurableSet_Icc
    have hcos' : ∀ x ∈ Icc 0 π, HasDerivWithinAt cos (-sin x) (Icc 0 π) x := by {
      have h_1 : ∀ x, HasDerivAt cos (-sin x) x := by exact fun x ↦ hasDerivAt_cos x
      exact fun x a ↦ HasDerivAt.hasDerivWithinAt (h_1 x)
    }
    have hcos : InjOn cos (Icc 0 π) := by exact injOn_cos
    have hsin₁ : ∀ x ∈ Icc 0 π, sin x ≥ 0 := by exact fun x a ↦ sin_nonneg_of_mem_Icc a
    have hsin₂ : ∀ x ∈ Icc 0 π, -sin x ≤ 0 := by {
      intro x hx
      have h1 : sin x ≥ 0 := by exact hsin₁ x hx
      exact Right.neg_nonpos_iff.mpr (hsin₁ x hx)
    }
    have hsin₃ : ∀ x ∈ Icc 0 π, sin x = |-sin x| := by {
      unfold abs
      simp
      intro x hx₁ hx₂
      exact sin_nonneg_of_nonneg_of_le_pi hx₁ hx₂
    }
    calc
    ∫ (x : ℝ) in (0)..π, sin x * f (cos x) = ∫ (x : ℝ) in Icc 0 π, sin x * f (cos x) := by sorry
    /- How are intervals in double point notation even defined? I tried proving the statement above
    with an 'exact?' or an 'rw?', but it neither worked for replacing (0)..π by Icc 0 π, nor Ioo 0 π, nor Ico 0 π, nor Ioc 0 π.
    What am I doing wrong here?-/
    _ = ∫ x in Icc 0 π, |(-sin x)| * f (cos x) := by sorry
    /- I don't know how to apply the fact hsin₃ inside the integral here...-/
    _ = ∫ y in image cos (Icc 0 π), f (y) := by exact Eq.symm (integral_image_eq_integral_abs_deriv_smul h₂ hcos' hcos f)
    _ = ∫ y in Icc (-1) (1), f y := by exact congrFun (congrArg integral (congrArg volume.restrict h₁)) fun y ↦ f y
    _ = ∫ (y : ℝ) in (-1)..1, f y := by sorry
    /- Same problem as before -/
  }
