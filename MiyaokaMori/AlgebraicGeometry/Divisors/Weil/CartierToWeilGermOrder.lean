import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor

/-! # The order of a Cartier divisor at a point as a sheaf morphism

The **canonical** construction of the order (Weil coefficient) of a Cartier divisor at a point `x`: on an
integral locally Noetherian scheme `X`, `ord_x : 𝒦^*/O^* ⟶ skyscraper_x(ℤ)` as a morphism of sheaves, given
by the universal property of the cokernel (Fulton §2.1; Stacks 02ST, the Weil divisor associated with a
Cartier divisor).

Route (no `Classical.choice` in the data):
1. The order on stalks, `stalkOrdHom x : (𝒦^*)_x ⟶ ℤ`, by `colimit.desc`: on every open `U ∋ x` take
   `t ↦ ord_x (t|_η)` (`rationalUnitsSectionToFunctionField U t` restricts the section to the generic point;
   `rationalUnitsSectionToFunctionField_res` gives compatibility).
2. Germs of units are killed: `O^*(U) → 𝒦^*(U) → K(X)` is the germ map `germToFunctionField`, and units have
   order `0` (Mathlib `Scheme.ord_of_isUnit`).
3. From the stalk to the skyscraper sheaf: `toSkyscraperPresheaf x (stalkOrdHom x) : 𝒦^* ⟶ skyscraper_x(ℤ)`,
   whose composite with `O^* → 𝒦^*` is `0` (step 2).
4. Descend through `cokernel.desc`: `ordSkyscraperDesc x : 𝒦^*/O^* ⟶ skyscraper_x(ℤ)` (in
   `Sheaf AddCommGrpCat`, where `TopCat.Sheaf.quotient` is this cokernel).
5. Evaluate on `⊤`: `quotientOrd x : Γ(X, 𝒦^*/O^*) →+ ℤ`.
Formula `quotientOrd_eq_of_restrict_eq`: `D|_U = π(t)` and `x ∈ U` give `quotientOrd x D = ord_x (t|_η)`
(`cokernel.π_desc`, and restrictions of the skyscraper sheaf are `eqToHom`).

No local equation is chosen and no inverse of a bijection is used: `weilCoefficient` (`CartierToWeil`) is
`quotientOrd x D`. `ℤ` is lifted to `Type u` (`ULift`) to live in `AddCommGrpCat.{u}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry Classical

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : AlgebraicGeometry.Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- The sheaf of units of rational functions in additive notation, `Additive 𝒦^*` (the cokernel of
`TopCat.Sheaf.quotient` is taken on this side). -/
abbrev rationalUnitsAddSheaf : TopCat.Sheaf AddCommGrpCat.{u} (X : TopCat.{u}) :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology (X : TopCat.{u}))
    commGroupAddCommGroupEquivalence.functor).obj X.rationalFunctionsUnitsSheaf

/-- The legs of the cocone: `t ∈ 𝒦^*(U)` (`x ∈ U`) `↦ ord_x (t|_η)`, an additive homomorphism. -/
def ordSectionAddHom (x : X) (U : X.Opens) (hx : x ∈ U) :
    Additive (X.rationalFunctionsUnitsSheaf.obj.obj (op U)) →+ ULift.{u} ℤ :=
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  AddMonoidHom.mk'
    (fun t => ULift.up (X.ord (X.rationalUnitsSectionToFunctionField U (Additive.toMul t) :
      X.functionField) x))
    (by
      intro a b
      apply ULift.ext
      change X.ord (X.rationalUnitsSectionToFunctionField U (Additive.toMul a * Additive.toMul b) :
        X.functionField) x = _
      rw [map_mul, Units.val_mul]
      exact X.ord_mul (Units.ne_zero _) (Units.ne_zero _))

theorem ordSectionAddHom_apply (x : X) (U : X.Opens) (hx : x ∈ U)
    (t : X.rationalFunctionsUnitsSheaf.obj.obj (op U)) :
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    X.ordSectionAddHom x U hx (Additive.ofMul t) =
      ULift.up (X.ord (X.rationalUnitsSectionToFunctionField U t : X.functionField) x) := rfl

/-- The cocone to `ℤ`: legs `ordSectionAddHom`, compatibility `rationalUnitsSectionToFunctionField_res`. -/
def ordCocone (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ X.rationalUnitsAddSheaf.presheaf) where
  pt := AddCommGrpCat.of (ULift.{u} ℤ)
  ι :=
    { app := fun U => AddCommGrpCat.ofHom (X.ordSectionAddHom x U.unop.1 U.unop.2)
      naturality := by
        intro U W inc
        ext a
        have : Nonempty U.unop.1 := ⟨⟨x, U.unop.2⟩⟩
        have : Nonempty W.unop.1 := ⟨⟨x, W.unop.2⟩⟩
        have hWU : W.unop.1 ≤ U.unop.1 := leOfHom ((OpenNhds.inclusion x).map inc.unop)
        change ULift.up (X.ord (X.rationalUnitsSectionToFunctionField W.unop.1
          (X.rationalFunctionsUnitsSheaf.obj.map (homOfLE hWU).op
            (Additive.toMul a)) : X.functionField) x) =
          ULift.up (X.ord (X.rationalUnitsSectionToFunctionField U.unop.1
            (Additive.toMul a) : X.functionField) x)
        rw [X.rationalUnitsSectionToFunctionField_res U.unop.1 W.unop.1 hWU] }

/-- The order on the stalk, `(Additive 𝒦^*)_x ⟶ ℤ` (`colimit.desc`). -/
def stalkOrdHom (x : X) :
    X.rationalUnitsAddSheaf.presheaf.stalk x ⟶ AddCommGrpCat.of (ULift.{u} ℤ) :=
  colimit.desc _ (X.ordCocone x)

theorem stalkOrdHom_germ (x : X) (U : X.Opens) (hx : x ∈ U)
    (a : X.rationalUnitsAddSheaf.obj.obj (op U)) :
    X.stalkOrdHom x (X.rationalUnitsAddSheaf.presheaf.germ U x hx a) =
      X.ordSectionAddHom x U hx a := by
  have h := congrArg (fun φ => φ.hom a) (colimit.ι_desc (X.ordCocone x) (op ⟨U, hx⟩))
  exact h


/-- The sheaf of units in additive notation, `Additive O^*`. -/
abbrev unitsAddSheaf : TopCat.Sheaf AddCommGrpCat.{u} (X : TopCat.{u}) :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology (X : TopCat.{u}))
    commGroupAddCommGroupEquivalence.functor).obj X.unitsSheaf

/-- `Additive O^* ⟶ Additive 𝒦^*`; `TopCat.Sheaf.quotient (unitsSheafToRationalFunctionsUnits X)` is its cokernel. -/
abbrev unitsToRationalUnitsAdd : X.unitsAddSheaf ⟶ X.rationalUnitsAddSheaf :=
  (CategoryTheory.sheafCompose (Opens.grothendieckTopology (X : TopCat.{u}))
    commGroupAddCommGroupEquivalence.functor).map X.unitsSheafToRationalFunctionsUnits

omit [IsLocallyNoetherian X] in
/-- The image in `𝒦^*(U)` of a unit section `u ∈ O^*(U)`, restricted to the generic point, is the germ
`germToFunctionField U u`. Scheme-level version; the same fact for varieties is
`CartierDivisor.val_rationalUnitsSectionToFunctionField_unitsSheafToRationalFunctionsUnits`
(`CartierDivisorOfLocalDataUnits`, stated for `X : Variety k`), which cannot be reused here since this module
is about arbitrary integral schemes. -/
theorem rationalUnitsSectionToFunctionField_unitsSheafToRationalFunctionsUnits
    (U : X.Opens) [Nonempty U] (u : (Γ(X, U))ˣ) :
    (X.rationalUnitsSectionToFunctionField U
        (X.unitsSheafToRationalFunctionsUnits.hom.app (op U) u) : X.functionField) =
      X.germToFunctionField U (u : Γ(X, U)) := by
  have hu : ((show (X.rationalFunctionsSheaf.obj.obj (op U))ˣ from
        X.unitsSheafToRationalFunctionsUnits.hom.app (op U) u) : X.rationalFunctionsSheaf.obj.obj (op U)) =
      X.toRationalFunctionsSheaf.hom.app (op U) (u : Γ(X, U)) := rfl
  change (X.rationalSectionToFunctionField U).hom
    ((show (X.rationalFunctionsSheaf.obj.obj (op U))ˣ from
        X.unitsSheafToRationalFunctionsUnits.hom.app (op U) u) : X.rationalFunctionsSheaf.obj.obj (op U)) = _
  rw [hu]
  exact congrArg (fun φ => φ.hom (u : Γ(X, U)))
    (X.toRationalFunctionsSheaf_rationalSectionToFunctionField U)

/-- Germs of units have order `0` (Mathlib `Scheme.ord_of_isUnit`). -/
theorem stalkOrdHom_germ_units (x : X) (U : X.Opens) (hx : x ∈ U)
    (a : X.unitsAddSheaf.obj.obj (op U)) :
    X.stalkOrdHom x (X.rationalUnitsAddSheaf.presheaf.germ U x hx
      (X.unitsToRationalUnitsAdd.hom.app (op U) a)) = 0 := by
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  rw [X.stalkOrdHom_germ]
  have hval : X.unitsToRationalUnitsAdd.hom.app (op U) a =
      Additive.ofMul (X.unitsSheafToRationalFunctionsUnits.hom.app (op U) (Additive.toMul a)) := rfl
  rw [hval, X.ordSectionAddHom_apply]
  apply ULift.ext
  change X.ord (X.rationalUnitsSectionToFunctionField U
    (X.unitsSheafToRationalFunctionsUnits.hom.app (op U)
      (show (Γ(X, U))ˣ from Additive.toMul a)) : X.functionField) x = 0
  rw [X.rationalUnitsSectionToFunctionField_unitsSheafToRationalFunctionsUnits U]
  exact X.ord_of_isUnit (show (Γ(X, U))ˣ from Additive.toMul a).isUnit hx

/-- `Additive 𝒦^* ⟶ skyscraper_x(ℤ)`: the order on the stalk through `toSkyscraperPresheaf`. -/
def ordToSkyscraper (x : X) :
    X.rationalUnitsAddSheaf ⟶ skyscraperSheaf x (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  CategoryTheory.ObjectProperty.homMk
    (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x (X.stalkOrdHom x))

theorem ordToSkyscraper_app (x : X) (U : X.Opens) (hx : x ∈ U) (a : X.rationalUnitsAddSheaf.obj.obj (op U)) :
    (X.ordToSkyscraper x).hom.app (op U) a =
      (eqToHom (if_pos hx).symm : AddCommGrpCat.of (ULift.{u} ℤ) ⟶
          (skyscraperPresheaf x (AddCommGrpCat.of (ULift.{u} ℤ))).obj (op U))
        (X.stalkOrdHom x (X.rationalUnitsAddSheaf.presheaf.germ U x hx a)) := by
  have happ : (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x (X.stalkOrdHom x)).app (op U) =
      X.rationalUnitsAddSheaf.presheaf.germ U x hx ≫ X.stalkOrdHom x ≫
        eqToHom (if_pos hx).symm := dif_pos hx
  change (StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x (X.stalkOrdHom x)).app (op U) a = _
  rw [happ]
  rfl

/-- `O^* → 𝒦^* → skyscraper_x(ℤ)` is the zero morphism. -/
theorem unitsToRationalUnitsAdd_comp_ordToSkyscraper (x : X) :
    X.unitsToRationalUnitsAdd ≫ X.ordToSkyscraper x = 0 := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  by_cases hx : x ∈ U.unop
  · ext a
    change (X.ordToSkyscraper x).hom.app U (X.unitsToRationalUnitsAdd.hom.app U a) = 0
    rw [X.ordToSkyscraper_app x U.unop hx, X.stalkOrdHom_germ_units x U.unop hx, map_zero]
    rfl
  · exact ((if_neg hx).symm.ndrec terminalIsTerminal :
      IsTerminal ((skyscraperPresheaf x (AddCommGrpCat.of (ULift.{u} ℤ))).obj U)).hom_ext _ _


/-- Descent to the quotient: `𝒦^*/O^* ⟶ skyscraper_x(ℤ)` (universal property of the cokernel;
`TopCat.Sheaf.quotient` is this cokernel in multiplicative notation). -/
def ordSkyscraperDesc (x : X) :
    cokernel X.unitsToRationalUnitsAdd ⟶ skyscraperSheaf x (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  cokernel.desc _ (X.ordToSkyscraper x) (X.unitsToRationalUnitsAdd_comp_ordToSkyscraper x)

theorem cokernelπ_ordSkyscraperDesc_app (x : X) (U : X.Opens)
    (a : X.rationalUnitsAddSheaf.obj.obj (op U)) :
    (X.ordSkyscraperDesc x).hom.app (op U)
        ((cokernel.π X.unitsToRationalUnitsAdd).hom.app (op U) a) =
      (X.ordToSkyscraper x).hom.app (op U) a :=
  congrArg (fun φ => φ.hom.app (op U) a)
    (cokernel.π_desc X.unitsToRationalUnitsAdd (X.ordToSkyscraper x)
      (X.unitsToRationalUnitsAdd_comp_ordToSkyscraper x))

/-- The order at `x` of a global section of the quotient sheaf `𝒦^*/O^*` (in multiplicative notation, i.e. of
a Cartier divisor): evaluate `ordSkyscraperDesc x` on `⊤` and read off the integer through
`skyscraper(⊤) = ℤ` (`eqToHom`). No local equation is chosen and no inverse of a bijection is used;
`quotientOrd_eq_of_restrict_eq` computes it from a local equation. -/
def quotientOrd (x : X)
    (D : (TopCat.Sheaf.quotient X.unitsSheafToRationalFunctionsUnits).obj.obj (op ⊤)) : ℤ :=
  ((eqToHom (if_pos (show x ∈ (⊤ : X.Opens) from trivial)) :
      (skyscraperPresheaf x (AddCommGrpCat.of (ULift.{u} ℤ))).obj (op ⊤) ⟶
        AddCommGrpCat.of (ULift.{u} ℤ)).hom
    ((X.ordSkyscraperDesc x).hom.app (op ⊤)
      (Multiplicative.toAdd
        (show Multiplicative ((cokernel X.unitsToRationalUnitsAdd).obj.obj (op ⊤)) from D)))).down

/-- Computation: if `D|_U = π(t)` (`t ∈ 𝒦^*(U)`, `x ∈ U`), then `quotientOrd x D = ord_x (t|_η)`. -/
theorem quotientOrd_eq_of_restrict_eq (x : X) (U : X.Opens) (hx : x ∈ U)
    (D : (TopCat.Sheaf.quotient X.unitsSheafToRationalFunctionsUnits).obj.obj (op ⊤))
    (t : X.rationalFunctionsUnitsSheaf.obj.obj (op U))
    (h : (TopCat.Sheaf.quotient X.unitsSheafToRationalFunctionsUnits).obj.map
        (homOfLE (show U ≤ ⊤ from le_top)).op D =
      (TopCat.Sheaf.quotientπ X.unitsSheafToRationalFunctionsUnits).hom.app (op U) t) :
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    X.quotientOrd x D = X.ord (X.rationalUnitsSectionToFunctionField U t : X.functionField) x := by
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  let cok := cokernel X.unitsToRationalUnitsAdd
  let D' : cok.obj.obj (op ⊤) :=
    Multiplicative.toAdd (show Multiplicative (cok.obj.obj (op ⊤)) from D)
  have hadd : cok.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op D' =
      (cokernel.π X.unitsToRationalUnitsAdd).hom.app (op U) (Additive.ofMul t) :=
    congrArg (fun z => Multiplicative.toAdd (show Multiplicative (cok.obj.obj (op U)) from z)) h
  have hnat : (X.ordSkyscraperDesc x).hom.app (op U)
        (cok.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op D') =
      (skyscraperPresheaf x (AddCommGrpCat.of (ULift.{u} ℤ))).map
        (homOfLE (show U ≤ ⊤ from le_top)).op ((X.ordSkyscraperDesc x).hom.app (op ⊤) D') :=
    congrArg (fun φ => φ.hom D')
      ((X.ordSkyscraperDesc x).hom.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  have hsky : (skyscraperPresheaf x (AddCommGrpCat.of (ULift.{u} ℤ))).map
        (homOfLE (show U ≤ ⊤ from le_top)).op =
      eqToHom (by rw [skyscraperPresheaf_obj, skyscraperPresheaf_obj, if_pos hx,
        if_pos (show x ∈ (⊤ : X.Opens) from trivial)]) := dif_pos hx
  have hnat' : (X.ordSkyscraperDesc x).hom.app (op U)
        ((cokernel.π X.unitsToRationalUnitsAdd).hom.app (op U) (Additive.ofMul t)) =
      (skyscraperPresheaf x (AddCommGrpCat.of (ULift.{u} ℤ))).map
        (homOfLE (show U ≤ ⊤ from le_top)).op ((X.ordSkyscraperDesc x).hom.app (op ⊤) D') :=
    (congrArg (fun z => (X.ordSkyscraperDesc x).hom.app (op U) z) hadd).symm.trans hnat
  have h1 : (X.ordSkyscraperDesc x).hom.app (op U)
        ((cokernel.π X.unitsToRationalUnitsAdd).hom.app (op U) (Additive.ofMul t)) =
      (eqToHom (if_pos hx).symm : AddCommGrpCat.of (ULift.{u} ℤ) ⟶
          (skyscraperPresheaf x (AddCommGrpCat.of (ULift.{u} ℤ))).obj (op U)).hom
        (ULift.up (X.ord (X.rationalUnitsSectionToFunctionField U t : X.functionField) x)) :=
    (X.cokernelπ_ordSkyscraperDesc_app x U (Additive.ofMul t)).trans
      ((X.ordToSkyscraper_app x U hx (Additive.ofMul t)).trans
        (congrArg (fun z => (eqToHom (if_pos hx).symm : AddCommGrpCat.of (ULift.{u} ℤ) ⟶
          (skyscraperPresheaf x (AddCommGrpCat.of (ULift.{u} ℤ))).obj (op U)).hom z)
          (X.stalkOrdHom_germ x U hx (Additive.ofMul t))))
  have hsky' := congrArg (fun φ => φ.hom ((X.ordSkyscraperDesc x).hom.app (op ⊤) D')) hsky
  have key0 := hsky'.symm.trans (hnat'.symm.trans h1)
  have key := congrArg (fun z => (eqToHom (if_pos hx) :
      (skyscraperPresheaf x (AddCommGrpCat.of (ULift.{u} ℤ))).obj (op U) ⟶
        AddCommGrpCat.of (ULift.{u} ℤ)).hom z) key0
  have e1 : ∀ (A B C : AddCommGrpCat.{u}) (p : A = B) (q : B = C) (a : A),
      (eqToHom q).hom ((eqToHom p).hom a) = (eqToHom (p.trans q)).hom a := by
    intro A B C p q a
    subst p; subst q; rfl
  have e2 : ∀ (A : AddCommGrpCat.{u}) (p : A = A) (a : A), (eqToHom p).hom a = a := by
    intro A p a
    rw [eqToHom_refl]; rfl
  have key1 := (e1 _ _ _ _ _ _).symm.trans (key.trans ((e1 _ _ _ _ _ _).trans (e2 _ _ _)))
  exact congrArg ULift.down key1

end AlgebraicGeometry.Scheme

end
