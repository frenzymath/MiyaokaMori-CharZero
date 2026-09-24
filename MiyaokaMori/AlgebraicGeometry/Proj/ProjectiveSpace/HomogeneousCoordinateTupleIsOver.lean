import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateSections
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple

/-! # A morphism with a homogeneous coordinate tuple is a `k`-morphism

`IsHomogeneousCoordinateTuple e f coord → f.IsOver (Spec k)`.

Source: §2 of the paper (Section 2), the homogeneous coordinates `f_0, …, f_N` of `f`; the
projectivization morphism of a nowhere-zero tuple is a `k`-morphism (`projectivizationMorphism_comp_over`).

Proof. The hypothesis `hcoord` says `projectivizationMorphism (seedLineBundle e f) coord h = f ≫ e.emb`; the
projectivization morphism composed with `P^N ↘ Spec k` is `C ↘ Spec k`, and
`e.emb ≫ (P^N ↘ Spec k) = X ↘ Spec k` (`e.over`), hence `f ≫ (X ↘ Spec k) = C ↘ Spec k`.

This is used by the relative tangent sequence of the cone: `seedSection_comp_puncturedConeToProduct` needs
`[f.IsOver (Spec k)]`, which is not among the hypotheses of `cone_tangent_shortExact` but follows from `hcoord`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem IsHomogeneousCoordinateTuple.comp_over {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (f : C ⟶ X)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord) :
    f ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) = C ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := by
  obtain ⟨h, hproj⟩ := hcoord
  have := projectivizationMorphism_comp_over (k := k) (seedLineBundle e f) coord h
  rw [hproj, Category.assoc, e.over] at this
  exact this

theorem IsHomogeneousCoordinateTuple.isOver {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (f : C ⟶ X)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord) :
    f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨IsHomogeneousCoordinateTuple.comp_over e f coord hcoord⟩

end
