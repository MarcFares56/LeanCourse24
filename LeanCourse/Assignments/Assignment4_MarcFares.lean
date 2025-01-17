import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 4, sections 2, 3.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- Do the exercises about sets from last exercise set, if you haven't done them because
we didn't cover the material in class yet. -/


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by {
  sorry
  }


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  sorry
  }

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
  ext
  · simp
  · simp
    ring
  }

/- `A ≃ B` means that there is a bijection from `A` to `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
This is an exercise about finding lemmas from the library.
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
If you want, you can use `calc` blocks with `≃`. -/
example : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by {
  sorry
  }

/- Prove a version of the axiom of choice Lean's `Classical.choose`. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by {
  sorry
  }


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
    intro ε epos
    rcases hs ε epos with ⟨N1,s1⟩
    rcases hr N1 with ⟨N2,hn⟩
    use N2
    intro n N
    simp
    have : r n ≥ N1 := by apply hn n N
    apply s1 at this
    exact this
  }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
      intro ε epos
      rcases hs₁ ε epos with ⟨N1,hs1⟩
      rcases hs₃ ε epos with ⟨N3,hs3⟩
      let N := max N1 N3
      use N
      intro n hn
      rw[abs_lt]
      have : N1 ≤ N := by exact le_max_left N1 N3
      have : N1 ≤ n := by apply le_trans this hn
      have le1 : -ε < s₁ n - a ∧ s₁ n - a < ε := by exact abs_lt.1 (hs1 n this)

      have : N3 ≤ N := by exact Nat.le_max_right N1 N3
      have : N3 ≤ n := by apply le_trans this hn
      have le3 : -ε < s₃ n - a ∧ s₃ n - a < ε := by exact abs_lt.1 (hs3 n this)

      constructor
      · calc
        s₂ n - a ≥ s₁ n - a := by exact tsub_le_tsub_right (hs₁s₂ n) a
               _ > - ε := by exact le1.left
      · calc
        s₂ n - a ≤ s₃ n - a := by exact tsub_le_tsub_right (hs₂s₃ n) a
               _ < ε := by exact le3.right
    }
#check abs_lt
/- ## Sets -/

#leansearch "x ∈ s → f x ∈ f '' s."

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
  ext y
  constructor
  · intro ⟨h0,h1⟩
    simp at h0
    rcases h0 with ⟨x₀,⟨h01,h02⟩⟩
    simp; use x₀
    exact ⟨⟨h01,mem_of_eq_of_mem h02 h1⟩,h02⟩
  · intro h
    simp at h
    rcases h with ⟨x₀,⟨⟨h0,h1⟩,h2⟩⟩
    constructor
    · use x₀
    · exact mem_of_eq_of_mem (id (Eq.symm h2)) h1
  }

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
  ext x
  constructor
  simp
  intro h
  have q0 : 4^2 ≤ x^2 := by{
    calc
    4^2 = 16 := by norm_num
    _ ≤ x^2 := by exact h
    }
  by_cases q : x ≥ 0
  · right
    calc
    4 ≤ √(x^2) := by apply le_sqrt_of_sq_le q0
    _ = x := by exact sqrt_sq q
  · left
    simp at q
    have q3 : 4 ≤ -x := by {
    calc
    4 ≤ √(x^2) := by apply le_sqrt_of_sq_le q0
    _ = |x| := by apply sqrt_sq_eq_abs
    _ = -x := by exact abs_of_neg q
    }
    exact le_neg_of_le_neg q3
  · rintro h
    have : |x| ≥ 4 := by exact le_abs'.mpr h
    have q0 : |x|^2 ≥ 16 := by{
      calc
      |x|^2 ≥ 4^2 := by gcongr
          _ = 16 := by norm_num
    }
    have : |x|^2 = x^2 := by exact sq_abs x
    rw [this] at q0
    exact q0
  }

/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
  let g : β → α := invFunOn f s
  use g
  intro x h
  apply Set.InjOn.leftInvOn_invFunOn hf h
  }

lemma inverse_on_a_set' [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
  use fun y ↦ if ok : ∃ x ∈ s, f x = y then choose ok else default
  }


#leansearch "invFunOn (f x)=x."
/- Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

To help you along the way, some potentially useful ways to reformulate the hypothesis are given. -/

-- This lemma might be useful.
#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
  -- h1' and h1'' might be useful later as arguments of `simp` to simplify your goal.
  have h1' : ∀ x y, f x ≠ g y := by{
    by_contra h; simp at h
    rcases h with ⟨x,y,h⟩
    have : f x ∈ range f ∩ range g := by exact ⟨mem_range_self x, mem_of_eq_of_mem h (mem_range_self y)⟩
    rw[h1] at this; exact this
  }
  have h1'' : ∀ y x, g y ≠ f x := by exact fun y x a ↦ h1' x y (id (Eq.symm a))
  have h2' : ∀ x, x ∈ range f ∪ range g := by {
    intro x; rw[h2]; exact trivial
  }

  let L : Set α × Set β → Set γ := fun (s,t) => (f '' s) ∪ (g '' t)
  let R : Set γ → Set α × Set β := fun x => ((f ⁻¹' x), (g ⁻¹' x))

  use L,R
  constructor
  · ext S y
    have ids : id S = S := by exact rfl
    constructor
    · rintro (⟨x1,⟨q0,q1⟩⟩ | ⟨x2,⟨q0,q1⟩⟩)
      · simp at q0; rw[q1] at q0; rw[ids]; exact q0
      · simp at q0; rw[q1] at q0; rw[ids]; exact q0
    · intro h
      unfold R L; simp
      have yfg : y ∈ range f ∨ y ∈ range g := by exact h2' y
      rcases yfg with ⟨x,fx⟩ | ⟨x,fx⟩
      · left; use x; exact ⟨mem_of_eq_of_mem fx h, fx⟩
      · right; use x; exact ⟨mem_of_eq_of_mem fx h, fx⟩
  · ext S x
    have ids : id S = S := by exact rfl
    constructor
    · rintro (⟨x₀,r1,r2⟩|⟨x₀,r1,r2⟩)
      · have : x = x₀ := by exact hf (id (Eq.symm r2))
        rw[this]; exact r1
      · rw[ids]
        exact False.elim (h1' x x₀ (id (Eq.symm r2)))
    · intro h
      · left
        use x
        constructor
        · rw[ids] at h; exact h
        · rfl
    have ids : id S = S := by exact rfl
    constructor
    rintro (⟨x₀,⟨q1,q2⟩⟩|⟨x₀,⟨q1,q2⟩⟩)
    · exact False.elim (h1' x₀ x q2)
    · have q : x = x₀ := by exact hg (id (Eq.symm q2))
      rw[ids,q]; exact q1
    · intro h
      right
      use x
      constructor
      · rw[ids] at h; exact h
      · rfl
  }
