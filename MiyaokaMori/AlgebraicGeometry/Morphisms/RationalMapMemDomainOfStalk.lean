import MiyaokaMori.Prelude

/-! # Membership in the domain of a rational map via the local ring

Let `ψ : X ⤏ Y` be a rational map from an integral scheme, with `Y` locally of finite type over a base `S`.
If `Spec O_{X,x} → Y` is an `S`-morphism whose restriction to the function field is the function-field point
of `ψ`, then `x` lies in the domain of `ψ`.

Reference: Stacks Project, Tag 0BX6 (spreading out a morphism from the local ring to a neighbourhood);
Mathlib `PartialMap.ofFromSpecStalk`, `RationalMap.eq_of_fromFunctionField_eq`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- `fromSpecStalkOfMem` on an open subscheme `U ∋ x` is compatible with specialization:
`Spec.map (stalkSpecializes h) ≫ U.fromSpecStalkOfMem x = U.fromSpecStalkOfMem y` for `y ⤳ x`, `y ∈ U`.
Proof: `U.ι` is a monomorphism, and after composing with `U.ι` both sides are `X.fromSpecStalk y`
(`Opens.fromSpecStalkOfMem_ι`, `SpecMap_stalkSpecializes_fromSpecStalk`). -/
theorem AlgebraicGeometry.Scheme.Opens.SpecMap_stalkSpecializes_fromSpecStalkOfMem
    {X : Scheme.{u}} (U : X.Opens) {x y : X} (h : y ⤳ x) (hx : x ∈ U) (hy : y ∈ U) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx =
      U.fromSpecStalkOfMem y hy := by
  rw [← cancel_mono U.ι, Category.assoc, Opens.fromSpecStalkOfMem_ι, Opens.fromSpecStalkOfMem_ι,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- The function-field point of a partial map equals
`Spec (algebraMap (stalk x) K(X)) ≫ g.fromSpecStalkOfMem hx` for `x ∈ g.domain`.
Proof: `algebraMap (stalk x) K(X)` is by definition `stalkSpecializes` (`stalkFunctionFieldAlgebra`,
`RingHom.algebraMap_toAlgebra`); unfold `fromSpecStalkOfMem` and apply
`Opens.SpecMap_stalkSpecializes_fromSpecStalkOfMem`. -/
theorem AlgebraicGeometry.Scheme.PartialMap.fromFunctionField_eq_SpecMap_algebraMap_comp
    {X Y : Scheme.{u}} [IrreducibleSpace X] (g : X.PartialMap Y) {x : X} (hx : x ∈ g.domain) :
    g.fromFunctionField =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        g.fromSpecStalkOfMem hx := by
  have e : CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
    ext1
    exact RingHom.algebraMap_toAlgebra _
  rw [e]
  dsimp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem]
  rw [← Category.assoc, Opens.SpecMap_stalkSpecializes_fromSpecStalkOfMem]

/-- A point `x` of the integral scheme `X` lies in the domain of the rational map `ψ : X ⤏ Y` (with `Y`
locally of finite type over `S`) as soon as there is an `S`-morphism `h : Spec O_{X,x} ⟶ Y` whose
restriction to the function field is `ψ.fromFunctionField`.

Proof. Let `g := Scheme.PartialMap.ofFromSpecStalk (X ↘ S) (Y ↘ S) h hS`. Then
`PartialMap.mem_domain_ofFromSpecStalk` gives `x ∈ g.domain` and
`PartialMap.fromSpecStalkOfMem_ofFromSpecStalk` gives `g.fromSpecStalkOfMem _ = h`. By
`fromFunctionField_eq_SpecMap_algebraMap_comp`, `g.fromFunctionField = Spec.map (algebraMap) ≫ h`, so
`g.toRationalMap.fromFunctionField = ψ.fromFunctionField`; `RationalMap.eq_of_fromFunctionField_eq` gives
`g.toRationalMap = ψ`, and `RationalMap.mem_domain` concludes. -/
theorem AlgebraicGeometry.Scheme.RationalMap.mem_domain_of_fromSpecStalk
    {X Y S : Scheme.{u}} [X.Over S] [Y.Over S] [IsIntegral X] [LocallyOfFiniteType (Y ↘ S)]
    (ψ : X ⤏ Y) (x : X) (h : Spec (X.presheaf.stalk x) ⟶ Y)
    (hS : h ≫ (Y ↘ S) = X.fromSpecStalk x ≫ (X ↘ S))
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ h =
      ψ.fromFunctionField) :
    x ∈ ψ.domain := by
  set g : X.PartialMap Y := PartialMap.ofFromSpecStalk (X ↘ S) (Y ↘ S) h hS with hg
  have hx : x ∈ g.domain := PartialMap.mem_domain_ofFromSpecStalk (X ↘ S) (Y ↘ S) h hS
  have hfun : g.toRationalMap.fromFunctionField = ψ.fromFunctionField := by
    rw [RationalMap.fromFunctionField_toRationalMap, g.fromFunctionField_eq_SpecMap_algebraMap_comp hx,
      ← hgen]
    congr 1
    exact PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (X ↘ S) (Y ↘ S) h hS
  exact RationalMap.mem_domain.mpr ⟨g, hx, RationalMap.eq_of_fromFunctionField_eq _ _ hfun⟩

end
