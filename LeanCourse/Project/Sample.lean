/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/
section General


/-!
# Orientable Manifolds

This file defines orientable manifolds: a differentiable manifold is orientable if and only if it
admits an orientable atlas, i.e. an atlas whose transition functions have a strictly positive
Jacobian.

## Main Definitions

- `OrientationPreserving` : a map between normed spaces is orientation-preserving on a given set
  if the determinant of its Jacobian is strictly positive on that set.
- `OrientationReversing` : a map between normed spaces is orientation-reversing on a given set
  if the determinant of its Jacobian is strictly negative on that set.
- `orientationPreservingGroupoid` : the groupoid of partial homeos of `H` which are
  orientation-preserving.
- `OrientableManifold` : a type class saying that the charted space `M`, modelled on the space
  `H`, admits an orientation.
- `OrientableSmoothManifold` : a type class representing a manifold that is both orientable
  and smooth.

## Main Results

- `OrientationPreserving.differentiableAt` : an orientation preserving map is differentiable.
- `OrientationReversing.differentiableAt` : an orientation reversing map is differentiable.
- `orientationPreserving_comp` : a composition between two orientation preserving maps is
  orientation preserving.
- `orientationReversing_comp_orientationPreserving` : a composition between an orientation
  reversing map and an orientation preserving map is orientation reversing.
- `orientationPreserving_comp_orientationReversing` : a composition between an orientation
  preserving map and an orientation reversing map is orientation reversing.
- `orientationReversing_comp` : a composition between two orientation reversing maps is
  orientation preserving.
- `orientableManifold_of_zero_dim` : `0`-dimensional manifolds are always orientable.
- A finite-dimensional normed space is orientable (w.r.t. the trivial model).

## TODO

- Generalize this discussion to other fields, for example over `ℚ`.
- On a given connected set, a diffeomorphism is either orientation preserving or orientation
  reversing.
- A normed space (with the trivial model) is orientable.
- The `n`-sphere is orientable.
- Products of orientable manifolds are orientable.
- Define orientations of a smooth manifold, and show that a manifold is orientable if and only if it
  admits an orientation.
- Define orientation preserving and reversing maps between manifolds.

## Implementation notes

The current definitions work for differentiable manifolds. For topological manifolds, orientability
can be defined using *local* orientations (which mathlib cannot state yet, as there is no e.g.
singular homology). In the future, it would be nice to generalise these definitions to allow for
topological manifolds also, and relate them to the current definition.

-/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

section OrientationPreserving

/--
A map between normed spaces is orientation-preserving on a given set if it is differentiable and the
determinant of its Jacobian is strictly positive on that set.
-/
def OrientationPreserving (f : H → H) (s : Set H) : Prop :=
  ∀ x ∈ s, 0 < (fderiv ℝ f x).det

/--
A map between normed spaces is orientation-reversing on a given set if it is differentiable and the
determinant of its Jacobian is strictly negative on that set.
-/
def OrientationReversing (f : H → H) (s : Set H) : Prop :=
  ∀ x ∈ s, (fderiv ℝ f x).det < 0

lemma orientationPreserving_of_zero_dim (f : H → H) (s : Set H)
    (h : Module.finrank ℝ H = 0) : OrientationPreserving f s := by
  intro _ _
  simp [LinearMap.det_eq_one_of_finrank_eq_zero h]

lemma OrientationPreserving.differentiableAt [FiniteDimensional ℝ H] {f : H → H} {s : Set H}
    (h : OrientationPreserving f s) {x : H} (hs : x ∈ s) : DifferentiableAt ℝ f x := by
  cases subsingleton_or_nontrivial H
  · apply ((s.subsingleton_of_subsingleton).differentiableOn _ hs).differentiableAt
    exact mem_nhds_discrete.mpr hs
  · rw [OrientationPreserving] at h
    contrapose! h
    use x, hs
    rw [fderiv_zero_of_not_differentiableAt h, ContinuousLinearMap.det]
    simp [ne_of_gt Module.finrank_pos]

lemma OrientationReversing.differentiableAt {f : H → H} {s : Set H} (h : OrientationReversing f s)
    {x : H} (hs : x ∈ s) : DifferentiableAt ℝ f x := by
  rw [OrientationReversing] at h
  contrapose! h
  use x, hs
  rw [fderiv_zero_of_not_differentiableAt h, ContinuousLinearMap.det]
  simp [ne_of_gt Module.finrank_pos]

lemma orientationPreserving_id (s : Set H) : OrientationPreserving id s := by
  intro
  simp [ContinuousLinearMap.det]

lemma orientationPreserving_comp [FiniteDimensional ℝ H] {f g : H → H} {u v : Set H}
    (hf : OrientationPreserving f u) (hg : OrientationPreserving g v) :
    OrientationPreserving (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  simpa only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp]
    using mul_pos (hg (f x) hxv) (hf x hxu)

lemma orientationReversing_comp_orientationPreserving [FiniteDimensional ℝ H]
    {f g : H → H} {u v : Set H} (hf : OrientationPreserving f u) (hg : OrientationReversing g v) :
    OrientationReversing (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  simpa [ContinuousLinearMap.det] using mul_neg_of_neg_of_pos (hg (f x) hxv) (hf x hxu)

lemma orientationPreserving_comp_orientationReversing [FiniteDimensional ℝ H]
    {f g : H → H} {u v : Set H} (hf : OrientationReversing f u) (hg : OrientationPreserving g v) :
    OrientationReversing (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  simpa [ContinuousLinearMap.det] using mul_neg_of_pos_of_neg (hg (f x) hxv) (hf x hxu)

lemma orientationReversing_comp {f g : H → H} {u v : Set H}
    (hf : OrientationReversing f u) (hg : OrientationReversing g v) :
    OrientationPreserving (g ∘ f) (u ∩ f ⁻¹' v) := by
  intro x ⟨hxu, hxv⟩
  rw [fderiv.comp x (hg.differentiableAt hxv) (hf.differentiableAt hxu)]
  simpa only [ContinuousLinearMap.det, ContinuousLinearMap.coe_comp, LinearMap.det_comp]
    using mul_pos_of_neg_of_neg (hg (f x) hxv) (hf x hxu)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type*}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]

open Set

/-- The pregroupoid of orientation-preserving maps. -/
def orientationPreservingPregroupoid [FiniteDimensional ℝ E] : Pregroupoid H where
  property f s :=
    OrientationPreserving (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ interior (range I))
    -- The second condition states that "on `s`, `f` maps the interior of `M`
    -- to the interior of `M`": this can be proven superfluous in many contexts,
    -- but such a proof is currently out of reach for mathlib.
    -- Hence, we add this condition.
    ∧ (I.symm ⁻¹' s ∩ interior (range I)).image (I ∘ f ∘ I.symm) ⊆ interior (range I)
  comp {f g} U V hf hg _ _ _ := by
    refine ⟨fun x ⟨hx₁, hx₂⟩ ↦ ?_, fun y ⟨x, hx, _⟩ ↦ ?_⟩
    · have hx' : x ∈ I.symm ⁻¹' U ∩ interior (range I) ∩
          I ∘ f ∘ I.symm ⁻¹' (I.symm ⁻¹' V ∩ interior (range I)) :=
        ⟨⟨mem_of_mem_inter_left hx₁, hx₂⟩, by simp_all, by aesop⟩
      convert orientationPreserving_comp hf.1 hg.1 x hx'
      simp [Function.comp]
    · have : x ∈ I.symm ⁻¹' U ∩ interior (range I) :=
        ⟨mem_of_mem_inter_left (mem_of_mem_inter_left hx), mem_of_mem_inter_right hx⟩
      have : I (f (I.symm x)) ∈ I.symm ⁻¹' V ∩ interior (range I) :=
        ⟨by simp_all, hf.2 <| mem_image_of_mem (↑I ∘ f ∘ ↑I.symm) this⟩
      apply hg.2
      aesop
  id_mem := by
    dsimp
    constructor
    · have h_fderiv : ∀ x ∈ interior (range I), fderiv ℝ (I ∘ I.symm) x = fderiv ℝ id x := by
        intro x hx
        apply Filter.EventuallyEq.fderiv_eq
        exact Filter.eventually_of_mem (mem_interior_iff_mem_nhds.mp hx) (by simp)
      exact univ_inter _ ▸ fun x hx ↦ h_fderiv x hx ▸ orientationPreserving_id _ x hx
    · rw [univ_inter]
      rintro x ⟨x', hx', hx''⟩
      have : x = x' := hx'' ▸ I.right_inv (interior_subset hx')
      exact this ▸ hx'
  locality {f u} _ h :=
    And.intro
    (fun x hxu ↦ have ⟨v, _, hxv, h⟩ := h (I.symm x) hxu.1
    h.1 _ ⟨Set.mem_inter hxu.1 hxv, hxu.2⟩)
    (fun _ ⟨x, ⟨aux, hxint⟩, hx⟩ ↦ have ⟨v, _, hxv, ⟨_, hint⟩⟩ := h (I.symm x) aux
    hx ▸ hint (mem_image_of_mem (↑I ∘ f ∘ ↑I.symm) ⟨⟨aux, hxv⟩, hxint⟩))
  congr {f g u} hu fg hf := by
    have : EqOn (↑I ∘ g ∘ ↑I.symm) (↑I ∘ f ∘ ↑I.symm) (I.symm ⁻¹' u ∩ interior (range ↑I)) := by
      simp_all [EqOn]
    apply And.intro
    · intro x hx
      have : fderivWithin ℝ (↑I ∘ g ∘ ↑I.symm) (I.symm ⁻¹' u ∩ interior (range ↑I)) x
          = fderivWithin ℝ (↑I ∘ f ∘ ↑I.symm) (I.symm ⁻¹' u ∩ interior (range ↑I)) x :=
        fderivWithin_congr' this hx
      have : fderiv ℝ (↑I ∘ g ∘ ↑I.symm) x = fderiv ℝ (↑I ∘ f ∘ ↑I.symm) x := by
        rw [fderivWithin_of_isOpen, fderivWithin_of_isOpen] at this
        exact this
        rw [Set.inter_comm]
        apply ContinuousOn.isOpen_inter_preimage
        · exact ModelWithCorners.continuousOn_symm I
        · exact isOpen_interior
        exact hu
        exact hx
        rw [Set.inter_comm]
        apply ContinuousOn.isOpen_inter_preimage
        · exact ModelWithCorners.continuousOn_symm I
        · exact isOpen_interior
        exact hu
        exact hx
      exact this ▸ hf.1 x hx
    · exact Set.EqOn.image_eq this ▸ hf.2

/-- The groupoid of orientation-preserving maps. -/
def orientationPreservingGroupoid [FiniteDimensional ℝ E] : StructureGroupoid H :=
  (orientationPreservingPregroupoid I).groupoid

/-- The groupoid of orientation-preserving `n` times continuously differentiable maps -/
def contDiffOrientationPreservingGroupoid (n : ℕ∞) (I : ModelWithCorners ℝ E H)
    [FiniteDimensional ℝ E] : StructureGroupoid H :=
  (orientationPreservingGroupoid I) ⊓ (contDiffGroupoid n I)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)

/-- An identity partial homeomorphism belongs to the orientation-preserving groupoid. -/
theorem ofSet_mem_orientationPreservingGroupoid [FiniteDimensional ℝ E] {s : Set H}
    (hs : IsOpen s) : PartialHomeomorph.ofSet s hs ∈ orientationPreservingGroupoid I := by
  have h_fderiv : ∀ x ∈ interior (range I), fderiv ℝ (I ∘ I.symm) x = fderiv ℝ id x := by
    intro x hx
    apply Filter.EventuallyEq.fderiv_eq
    exact Filter.eventually_of_mem (mem_interior_iff_mem_nhds.mp hx) (by simp)
  refine ⟨⟨fun x hx ↦ h_fderiv x hx.2 ▸ orientationPreserving_id _ x hx.2, ?a⟩,
          fun x hx ↦ h_fderiv x hx.2 ▸ orientationPreserving_id _ x hx.2, ?a⟩
  rintro x ⟨x', hx', hx''⟩
  have : x = x' := hx'' ▸ I.right_inv (interior_subset hx'.2)
  exact this ▸ hx'.2

/--
The composition of a partial homeomorphism from `H` to `M` and its inverse belongs to the
orientation-preserving groupoid.
-/
theorem symm_trans_mem_orientationPreservingGroupoid [FiniteDimensional ℝ E]
    (e : PartialHomeomorph M H) : e.symm.trans e ∈ orientationPreservingGroupoid I :=
  have h : e.symm.trans e ≈ PartialHomeomorph.ofSet e.target e.open_target :=
    PartialHomeomorph.symm_trans_self _
  StructureGroupoid.mem_of_eqOnSource _ (ofSet_mem_orientationPreservingGroupoid I e.open_target) h

end OrientationPreserving

/-! ### Orientable manifolds -/

section OrientableManifold

/-- Typeclass defining orientable manifolds: a finite-dimensional (topological) manifold
is orientable if and only if it admits an orientable atlas. -/
class OrientableManifold {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E] (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] extends
  HasGroupoid M (orientationPreservingGroupoid I) : Prop

/-- `0`-dimensional manifolds are always orientable. -/
lemma orientableManifold_of_zero_dim {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = 0) :
    OrientableManifold I M where
  compatible {e₁ e₂} _ _ := by
    refine ⟨⟨orientationPreserving_of_zero_dim _ _ h, ?_⟩,
      orientationPreserving_of_zero_dim _ _ h, ?_⟩
    · by_cases hE : interior (Set.range I) = ∅
      · simp [hE]
      · rw [Set.subset_def]
        intro y hy
        rw [Set.eq_empty_iff_forall_not_mem] at hE
        push_neg at hE
        obtain ⟨x, hx⟩ := hE
        let s := I ∘ (e₁.symm.trans e₂) ∘ I.symm ''
          (I.symm ⁻¹' (e₁.symm.trans e₂).source ∩ interior (Set.range I))
        simp_all [(fun _ _ _ ↦ (Module.finrank_zero_iff.mp h).elim x y) s y hy]
    · by_cases hE : interior (Set.range I) = ∅
      · simp [hE]
      · rw [Set.subset_def]
        intro y hy
        rw [Set.eq_empty_iff_forall_not_mem] at hE
        push_neg at hE
        obtain ⟨x, hx⟩ := hE
        let s := I ∘ (e₁.symm.trans e₂).symm ∘ I.symm ''
          (I.symm ⁻¹' (e₁.symm.trans e₂).target ∩ interior (Set.range I))
        simp_all [(fun _ _ _ ↦ (Module.finrank_zero_iff.mp h).elim x y) s y hy]

/-- Typeclass defining orientable smooth manifolds: a smooth manifold is orientable
if and only if it admits an atlas which is both smooth and orientable -/
class OrientableSmoothManifold {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E] (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] extends
  HasGroupoid M (contDiffOrientationPreservingGroupoid ⊤ I) : Prop
#check SmoothManifoldWithCorners.prod
/-- A finite-dimensional normed space is an orientable smooth manifold. -/
instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {I : ModelWithCorners ℝ E E} : OrientableSmoothManifold I E :=
  { hasGroupoid_model_space _ _ with }

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
#check (MetricSpace X)
variable (𝕜 E)
lemma orientableManifold_of_product {E H : Type*} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [FiniteDimensional ℝ E] (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [OrientableSmoothManifold I M] [FiniteDimensional ℝ E'] (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M']
    [OrientableSmoothManifold I' M'] :
    OrientableSmoothManifold (I.prod I') (M × M') where
    compatible {e₁ e₂} _ _ := by{
      sorry
    }
end OrientableManifold
