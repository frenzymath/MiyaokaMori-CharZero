import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01pbAffineOpen
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveQuasiProjectiveProperSectionsGenerated

/-! # The section ring of a graded algebra generated in degree one is of finite type

If a graded quasi-coherent algebra `S` is generated in degree one and `S_1` is of finite type, then for
every affine open `V` of the base the graded section ring `A = Γ(V, S)` is a finite type `A_0`-algebra
(so Mathlib gives that `Proj A → Spec A_0` is quasi-compact and proper, and `Proj A` is compact).

References: Stacks 01NQ, 01O4, 07RL (`P(E) → S` is locally of finite type / quasi-compact). The two inputs
are `Modules.finite_sections_of_isFiniteType` (Stacks 01PB on an arbitrary affine open) and
`GradedQCAlgebra.adjoin_sectionsGrading_one_eq_top` (`ProjectiveQuasiProjectiveProperSectionsGenerated.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **The graded section ring is a finite type `A_0`-algebra.**
Let `S` be a graded quasi-coherent algebra on `X` with `S.GeneratedInDegreeOne` and `(S.part 1).IsFiniteType`,
let `V` be an affine open of `X`, `A := S.sectionsRing V`, `A_m := S.sectionsGrading V m`. Then
`Algebra.FiniteType A_0 A` (the `A_0`-algebra structure is Mathlib's `SetLike.GradeZero` instance,
`algebraMap A_0 A` the subtype inclusion).

**Proof**:
1. `S_1` is of finite type and quasi-coherent (`GradedQCAlgebra.quasicoherent`) and `V` is affine, so
   `Γ(V, S_1)` is a finitely generated `Γ(V, O_X)`-module (Stacks 01PB on an arbitrary affine open,
   `Modules.finite_sections_of_isFiniteType`). Take a finite generating set `s ⊆ Γ(V, S_1)`
   (`Module.Finite.fg_top`: `span s = ⊤`).
2. The action of `Γ(V, O_X)` on `A` factors through `A_0`: for `r ∈ Γ(V, O_X)` and `a ∈ Γ(V, S_1)`,
   `of 1 (r • a) = algebraMap A_0 A (sectionsUnit V r) * of 1 a` (`sectionsUnit_mul_of`).
3. By `adjoin_sectionsGrading_one_eq_top`, `adjoin A_0 A_1 = ⊤`. Let `B := adjoin A_0 (of 1 '' s)`.
   For `x ∈ A_1`, `x = of 1 a` with `a ∈ span s`; by induction on `span` (`Submodule.span_induction`): the
   generators `of 1 g ∈ B` (`subset_adjoin`), `0` and sums are in `B`, and `r • a` reduces by step 2 to
   `algebraMap A_0 A (sectionsUnit V r) * of 1 a`, while `B` contains the image of `algebraMap` and is
   closed under multiplication. Hence `A_1 ⊆ B`, `⊤ = adjoin A_0 A_1 ≤ B`, i.e. `B = ⊤`, and
   `Algebra.FiniteType A_0 A` (`Subalgebra.FG ⊤` with generating set `s.image (of 1)`).

**Edge cases**: for `V = ∅`, `A` is the zero ring, trivially of finite type; for `s = ∅` (`S_1|_V = 0`),
`adjoin A_0 ∅ = ⊥`, and step 3 gives `⊥ = ⊤`, trivial. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.finiteType_sectionsRing
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (hS : S.GeneratedInDegreeOne)
    (hfin : (S.part 1).IsFiniteType) (V : X.affineOpens) :
    Algebra.FiniteType (S.sectionsGrading V.1 0) (S.sectionsRing V.1) := by
  classical
  have : (S.part 1).IsQuasicoherent := S.quasicoherent 1
  have hmod : Module.Finite Γ(X, V.1) Γ(S.part 1, V.1) :=
    AlgebraicGeometry.Scheme.Modules.finite_sections_of_isFiniteType (S.part 1) V.2
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule Γ(X, V.1) Γ(S.part 1, V.1)).FG)
  -- `ι a = of 1 a`, with the domain spelled as `Γ(S.part 1, V)` (the spelling that carries the
  -- `Module Γ(X, V)` instance); `B` is the candidate finitely generated subalgebra.
  let ι : Γ(S.part 1, V.1) → S.sectionsRing V.1 := fun a => DirectSum.of (S.sectionsPiece V.1) 1 a
  let B : Subalgebra (S.sectionsGrading V.1 0) (S.sectionsRing V.1) :=
    Algebra.adjoin (S.sectionsGrading V.1 0) ((s.image ι : Finset (S.sectionsRing V.1)) : Set _)
  -- Step 2 + 3: every `of 1 a` lies in `B` (induction over `span s = ⊤`).
  have hB : ∀ a : Γ(S.part 1, V.1), ι a ∈ B := by
    intro a
    have ha : a ∈ Submodule.span Γ(X, V.1) (s : Set Γ(S.part 1, V.1)) := by
      rw [hs]; exact Submodule.mem_top
    refine Submodule.span_induction (p := fun a _ => ι a ∈ B) ?_ ?_ ?_ ?_ ha
    · intro g hg
      exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem ι hg))
    · have h0 : ι 0 = 0 := map_zero (DirectSum.of (S.sectionsPiece V.1) 1)
      exact (congrArg (fun z => z ∈ B) h0).mpr B.zero_mem
    · intro x y _ _ hx hy
      have h : ι (x + y) = ι x + ι y := map_add (DirectSum.of (S.sectionsPiece V.1) 1) x y
      exact (congrArg (fun z => z ∈ B) h).mpr (B.add_mem hx hy)
    · intro r x _ hx
      have h : ι (r • x) = ((S.sectionsUnit V.1 r : S.sectionsGrading V.1 0) : S.sectionsRing V.1) * ι x :=
        (S.sectionsUnit_mul_of V.1 r x).symm
      have h1 : ((S.sectionsUnit V.1 r : S.sectionsGrading V.1 0) : S.sectionsRing V.1) ∈ B :=
        B.algebraMap_mem (S.sectionsUnit V.1 r)
      exact (congrArg (fun z => z ∈ B) h).mpr (B.mul_mem h1 hx)
  -- Conclude: `⊤ = adjoin A_0 A_1 ≤ B`.
  refine ⟨⟨s.image ι, ?_⟩⟩
  rw [eq_top_iff, ← S.adjoin_sectionsGrading_one_eq_top hS V]
  apply Algebra.adjoin_le
  rintro x ⟨a, rfl⟩
  exact hB a

end
