import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.AffinePointClosureDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ReducedPointClosure
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueFieldBaseEquiv
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothCurveDimension
/-! # Dimension of the closure of a point and the transcendence degree of its residue field

For a scheme `X` locally of finite type over `k` (with the structure morphism packaged as a
`AlgebraicGeometry.Proj.SchemeOver k`) and any point `x`, `pointClosureDimension X x` (`= dim closure {x}`) equals
`trdeg_k κ(x)`, where the `k`-algebra structure on `κ(x)` is `pointBaseMap`. This is the corollary
form of Stacks 0A21 (6) (compare `height_eq_trdeg_residueField`).

Proof sketch:
1. `X` integral: take an affine open `U = Spec A` around the generic point (`A` a finitely generated
   `k`-domain); `spec_pointClosureDimension_eq_trdeg` gives `dim U = trdeg_k κ(η)`, and taking the
   supremum over an open cover gives `dim X = trdeg_k κ(η)`.
2. General `x`: pass to the reduced closure `Z = closure {x}` (integral, locally of finite type over
   `k` via `Z → X`); the closed immersion induces an isomorphism of residue fields at `x`
   (`closedImmersion_residueFieldMap_isIso`), so the transcendence degree is unchanged, and
   `ReducedPointClosure.dimension_eq` converts `dim Z` into `pointClosureDimension X x`.

The auxiliary lemmas `residueFieldMap_trdeg_eq_of_eq` and
`integral_dimension_eq_trdeg_of_genericPoint_eq` take the equation "generic point `= η`" as a
hypothesis which is substituted, because the algebra instances depend on the point.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Intersection

noncomputable section

namespace MiyaokaMori.PointClosureTrdeg

/-- For an irreducible scheme, the point-closure dimension of the generic point is the dimension
of the whole scheme. -/
theorem genericPoint_pointClosureDimension_eq (X : Scheme.{u}) [IrreducibleSpace X] :
    pointClosureDimension X (genericPoint X) = topologicalKrullDim X := by
  rw [pointClosureDimension_eq_topologicalKrullDim_closure, genericPoint_closure]
  exact IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
    (Homeomorph.Set.univ X).isHomeomorph

variable {k : Type u} [Field k]

/-- `residueFieldMap_trdeg_eq` with the image point written as an arbitrary point equal to it (the
algebra instances depend on the point, so the equation is substituted rather than rewritten). -/
theorem residueFieldMap_trdeg_eq_of_eq {X Y : AlgebraicGeometry.Proj.SchemeOver k}
    (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.toBase = X.toBase) (x : X.scheme)
    [IsIso (f.residueFieldMap x)] (y : Y.scheme) (hy : f.base x = y) :
    letI : Algebra k (Y.scheme.residueField y) := (pointBaseMap Y.toBase y).hom.toAlgebra
    letI : Algebra k (X.scheme.residueField x) := (pointBaseMap X.toBase x).hom.toAlgebra
    Algebra.trdeg k (Y.scheme.residueField y) = Algebra.trdeg k (X.scheme.residueField x) := by
  subst hy
  exact residueFieldMap_trdeg_eq f hf x

/-- For an integral scheme locally of finite type over `k`, every nonempty affine open has dimension
equal to the transcendence degree of the residue field of the generic point. -/
theorem isAffineOpen_dimension_eq_generic_trdeg
    (X : AlgebraicGeometry.Proj.SchemeOver k) [IsIntegral X.scheme] [LocallyOfFiniteType X.toBase]
    {U : X.scheme.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    letI : Algebra k (X.scheme.residueField (genericPoint X.scheme)) :=
      (pointBaseMap X.toBase (genericPoint X.scheme)).hom.toAlgebra
    topologicalKrullDim U =
      (Cardinal.toENat (Algebra.trdeg k
        (X.scheme.residueField (genericPoint X.scheme))) : WithBot ℕ∞) := by
  letI : Algebra k (X.scheme.residueField (genericPoint X.scheme)) :=
    (pointBaseMap X.toBase (genericPoint X.scheme)).hom.toAlgebra
  let Y : AlgebraicGeometry.Proj.SchemeOver k := ⟨Spec Γ(X.scheme, U), hU.fromSpec ≫ X.toBase⟩
  let j : Y.scheme ⟶ X.scheme := hU.fromSpec
  have hj : j ≫ X.toBase = Y.toBase := rfl
  have : Nonempty (Spec Γ(X.scheme, U)) :=
    Nonempty.map hU.isoSpec.hom inferInstance
  have : IsIntegral (Spec Γ(X.scheme, U)) :=
    isIntegral_of_isOpenImmersion hU.fromSpec
  let η := genericPoint (Spec Γ(X.scheme, U))
  letI : Algebra k ((Spec Γ(X.scheme, U)).residueField η) :=
    (pointBaseMap (hU.fromSpec ≫ X.toBase) η).hom.toAlgebra
  have hη : hU.fromSpec η = genericPoint X.scheme :=
    genericPoint_eq_of_isOpenImmersion hU.fromSpec
  have htr : Algebra.trdeg k (X.scheme.residueField (genericPoint X.scheme)) =
      Algebra.trdeg k ((Spec Γ(X.scheme, U)).residueField η) :=
    residueFieldMap_trdeg_eq_of_eq j hj η (genericPoint X.scheme) hη
  calc
    topologicalKrullDim U = topologicalKrullDim (Spec Γ(X.scheme, U)) :=
      IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
    _ = pointClosureDimension (Spec Γ(X.scheme, U)) η :=
      (genericPoint_pointClosureDimension_eq _).symm
    _ = (Cardinal.toENat
        (Algebra.trdeg k ((Spec Γ(X.scheme, U)).residueField η)) : WithBot ℕ∞) :=
      spec_pointClosureDimension_eq_trdeg Γ(X.scheme, U)
        (hU.fromSpec ≫ X.toBase) η
    _ = (Cardinal.toENat (Algebra.trdeg k
        (X.scheme.residueField (genericPoint X.scheme))) : WithBot ℕ∞) :=
      congrArg (fun c : Cardinal.{u} ↦ (Cardinal.toENat c : WithBot ℕ∞)) htr.symm

/-- An integral scheme locally of finite type over `k` has dimension equal to the transcendence
degree over `k` of the residue field of its generic point. -/
theorem integral_dimension_eq_trdeg
    (X : AlgebraicGeometry.Proj.SchemeOver k) [IsIntegral X.scheme] [LocallyOfFiniteType X.toBase] :
    letI : Algebra k (X.scheme.residueField (genericPoint X.scheme)) :=
      (pointBaseMap X.toBase (genericPoint X.scheme)).hom.toAlgebra
    topologicalKrullDim X.scheme =
      (Cardinal.toENat (Algebra.trdeg k
        (X.scheme.residueField (genericPoint X.scheme))) : WithBot ℕ∞) := by
  letI : Algebra k (X.scheme.residueField (genericPoint X.scheme)) :=
    (pointBaseMap X.toBase (genericPoint X.scheme)).hom.toAlgebra
  apply le_antisymm
  · apply AlgebraicGeometry.Scheme.dimension_le_of_open_neighborhoods
    intro x
    obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := X.scheme) (U := ⊤) (show x ∈ (⊤ : X.scheme.Opens) from trivial)
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    exact ⟨U, hx, (isAffineOpen_dimension_eq_generic_trdeg X hU).le⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty X.scheme)
    obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := X.scheme) (U := ⊤) (show x ∈ (⊤ : X.scheme.Opens) from trivial)
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [← isAffineOpen_dimension_eq_generic_trdeg X hU]
    exact topologicalKrullDim_subspace_le X.scheme (U : Set X.scheme)

/-- The previous theorem with the generic point written as an arbitrary point `η` equal to it (the
algebra instances depend on the point, so the equation is substituted rather than rewritten). -/
theorem integral_dimension_eq_trdeg_of_genericPoint_eq
    (X : AlgebraicGeometry.Proj.SchemeOver k) [IsIntegral X.scheme] [LocallyOfFiniteType X.toBase]
    (η : X.scheme) (hη : genericPoint X.scheme = η) :
    letI : Algebra k (X.scheme.residueField η) := (pointBaseMap X.toBase η).hom.toAlgebra
    topologicalKrullDim X.scheme =
      (Cardinal.toENat (Algebra.trdeg k (X.scheme.residueField η)) : WithBot ℕ∞) := by
  subst hη
  exact integral_dimension_eq_trdeg X

/-- For a scheme locally of finite type over `k`, the dimension of the closure of any point equals
the transcendence degree over `k` of its residue field (Stacks 0A21 (6)). -/
theorem pointClosureDimension_eq_trdeg
    (X : AlgebraicGeometry.Proj.SchemeOver k) [LocallyOfFiniteType X.toBase] (x : X.scheme) :
    letI : Algebra k (X.scheme.residueField x) := (pointBaseMap X.toBase x).hom.toAlgebra
    pointClosureDimension X.scheme x =
      (Cardinal.toENat (Algebra.trdeg k (X.scheme.residueField x)) : WithBot ℕ∞) := by
  letI : Algebra k (X.scheme.residueField x) := (pointBaseMap X.toBase x).hom.toAlgebra
  let Z : AlgebraicGeometry.Proj.SchemeOver k :=
    ⟨ReducedPointClosure.scheme X.scheme x, ReducedPointClosure.inclusion X.scheme x ≫ X.toBase⟩
  let i : Z.scheme ⟶ X.scheme := ReducedPointClosure.inclusion X.scheme x
  have hi : i ≫ X.toBase = Z.toBase := rfl
  let η := ReducedPointClosure.generic X.scheme x
  letI : Algebra k (Z.scheme.residueField η) := (pointBaseMap Z.toBase η).hom.toAlgebra
  have hη : genericPoint Z.scheme = η :=
    (genericPoint_spec Z.scheme).eq (ReducedPointClosure.generic_spec X.scheme x)
  have : IsIso (i.residueFieldMap η) :=
    closedImmersion_residueFieldMap_isIso i η
  have htr : Algebra.trdeg k (X.scheme.residueField x) =
      Algebra.trdeg k (Z.scheme.residueField η) :=
    residueFieldMap_trdeg_eq i hi η
  have hdim : topologicalKrullDim Z.scheme =
      (Cardinal.toENat (Algebra.trdeg k (Z.scheme.residueField η)) : WithBot ℕ∞) :=
    integral_dimension_eq_trdeg_of_genericPoint_eq Z η hη
  calc
    pointClosureDimension X.scheme x = topologicalKrullDim Z.scheme :=
      (ReducedPointClosure.dimension_eq X.scheme x).symm
    _ = (Cardinal.toENat (Algebra.trdeg k (Z.scheme.residueField η)) : WithBot ℕ∞) := hdim
    _ = (Cardinal.toENat (Algebra.trdeg k (X.scheme.residueField x)) : WithBot ℕ∞) :=
      congrArg (fun c : Cardinal.{u} ↦ (Cardinal.toENat c : WithBot ℕ∞)) htr.symm

/-- An open immersion over `k` preserves point-closure dimension when the target is locally of
finite type over `k`. -/
theorem pointClosureDimension_eq_of_isOpenImmersion
    {X Y : AlgebraicGeometry.Proj.SchemeOver k} (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.toBase = X.toBase)
    [IsOpenImmersion f]
    [LocallyOfFiniteType Y.toBase] (x : X.scheme) :
    pointClosureDimension X.scheme x = pointClosureDimension Y.scheme (f x) := by
  have : LocallyOfFiniteType X.toBase := by
    rw [← hf]
    infer_instance
  letI : Algebra k (X.scheme.residueField x) := (pointBaseMap X.toBase x).hom.toAlgebra
  letI : Algebra k (Y.scheme.residueField (f x)) :=
    (pointBaseMap Y.toBase (f x)).hom.toAlgebra
  rw [pointClosureDimension_eq_trdeg X x, pointClosureDimension_eq_trdeg Y (f x)]
  exact congrArg (fun c : Cardinal.{u} ↦ (Cardinal.toENat c : WithBot ℕ∞))
    (residueFieldMap_trdeg_eq f hf x).symm

end MiyaokaMori.PointClosureTrdeg

end
