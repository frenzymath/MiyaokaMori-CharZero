import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldEqResidueFieldAtGenericPoint

/-! # Degree of a dominant morphism

The degree `deg(V/W) = [K(V) : K(W)]` of a dominant morphism `f : V → W`; this is the field
extension degree appearing as the coefficient of the proper pushforward of cycles (Fulton,
*Intersection Theory*, §1.4).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree of `f : X ⟶ Y` between integral schemes: the residue degree at the generic point of
`X`. -/
noncomputable def functionFieldDegree {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y) : ℕ :=
  f.residueDegree (genericPoint X)

/-- When `f` is dominant (generic point to generic point), the degree is `[K(X) : K(Y)]` (with
`finrank = 0` for an infinite extension). -/

theorem functionFieldDegree_eq_finrank {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y)
    (hf : f.base (genericPoint X) = genericPoint Y) :
    functionFieldDegree f =
      @Module.finrank Y.functionField X.functionField _ _
        (@Algebra.toModule _ _ _ _
          (Y.functionFieldIsoResidueField.hom ≫ (Y.residueFieldCongr hf.symm).hom ≫
            f.residueFieldMap (genericPoint X) ≫ X.functionFieldIsoResidueField.inv).hom.toAlgebra) := by
  unfold functionFieldDegree AlgebraicGeometry.Scheme.Hom.residueDegree
  let x := genericPoint X
  let eY : Y.functionField ≅ Y.residueField (f x) :=
    Y.functionFieldIsoResidueField ≪≫ Y.residueFieldCongr hf.symm
  let eX : X.functionField ≅ X.residueField x :=
    X.functionFieldIsoResidueField
  let i : Y.residueField (f x) ≃+* Y.functionField := eY.symm.commRingCatIsoToRingEquiv
  let j : X.residueField x ≃+* X.functionField := eX.symm.commRingCatIsoToRingEquiv
  letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra Y.functionField X.functionField :=
    ((eY.hom ≫ f.residueFieldMap x ≫ eX.inv).hom.toAlgebra)
  have hc : (algebraMap Y.functionField X.functionField).comp i.toRingHom =
      j.toRingHom.comp (algebraMap (Y.residueField (f x)) (X.residueField x)) := by
    ext r
    change ((eY.hom ≫ f.residueFieldMap x ≫ eX.inv).hom) (i r) = j ((f.residueFieldMap x).hom r)
    have hi : i r = eY.symm.commRingCatIsoToRingEquiv r := rfl
    have hj : j ((f.residueFieldMap x).hom r) =
        eX.symm.commRingCatIsoToRingEquiv ((f.residueFieldMap x).hom r) := rfl
    rw [hi, hj]
    change eX.inv.hom ((f.residueFieldMap x).hom (eY.hom.hom
      (eY.symm.hom.hom r))) = eX.symm.hom.hom ((f.residueFieldMap x).hom r)
    have hey : eY.hom.hom (eY.symm.hom.hom r) = r := by
      exact eY.inv_hom_id_apply r
    rw [hey]
    rfl
  have hfin := Algebra.finrank_eq_of_equiv_equiv i j hc
  change Module.finrank (Y.residueField (f x)) (X.residueField x) = _
  exact hfin

end
