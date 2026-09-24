import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualCurry
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal

/-! # The dual commutes with pullback along isomorphisms

The dual sheaf commutes with pullback along an **isomorphism** `g : W ≅ T`: `g^*(E^∨) ≅ (g^*E)^∨`
(for every `E`, no local freeness required).

References: Stacks 01CM (the tensor–Hom adjunction `Hom(A ⊗ V, O) ≃ Hom(A, V^∨)` and its naturality,
`ModulesDualCurry`); Stacks 01CD (pullback is a strong monoidal functor); Mathlib
`Scheme.Modules.pullbackComp` / `pullbackId`. In the paper (the tangent sequence (2.2)
of §2.1) the trivialization `O ≅ T_{Tot(L)^×/(C×X)}` by the Euler vector field is transported along
the isomorphism `Z^× ≅ Tot(L)^×`, which needs this compatibility.

Proof (specific to isomorphisms, purely categorical):
1. `pullbackEquivalenceOfIsIso g : W.Modules ≌ T.Modules`: forward `Q := (g⁻¹)^*`, inverse `P := g^*`,
   unit and counit from `pullbackComp`, `pullbackId` and `g ≫ g⁻¹ = 𝟙`, `g⁻¹ ≫ g = 𝟙`
   (`Equivalence.mk` fixes the triangle identities with `adjointifyη`). Hence `Q ⊣ P`
   (`toAdjunction`), `P` is fully faithful (`fullyFaithfulInverse`), with unit `η_A : A ≅ P(QA)`.
2. For `A : W.Modules` there is a chain of bijections, all natural in `A`:
   `Hom(A, P(E^∨)) ≃ Hom(QA, E^∨)` (adjoint transpose) `≃ Hom(QA ⊗ E, O_T)` (inverse of `dualCurry`)
   `≃ Hom(P(QA ⊗ E), P O_T)` (`P` fully faithful) `≃ Hom(P(QA) ⊗ PE, O_W)` (monoidal isomorphisms
   `μ = pullbackTensorObjIso`, `ε = pullbackUnitIso`) `≃ Hom(A ⊗ PE, O_W)` (`η_A ▷ PE`)
   `≃ Hom(A, (PE)^∨)` (`dualCurry`). This is `dualPullbackHomEquiv`.
3. Naturality `dualPullbackHomEquiv_naturality`: piece by piece with
   `Adjunction.homEquiv_naturality_left_symm`, `dualCurry_symm_apply` (giving
   `dualCurry_symm_naturality_left`), `Functor.map_comp`, the naturality of `μ` in the left variable
   `pullback_μ_natural_left`, the naturality of the equivalence unit `Equivalence.unit_naturality`,
   and `dualCurry_naturality_left`.
4. `Yoneda.ext` turns this family of natural bijections into the isomorphism `P(E^∨) ≅ (PE)^∨`.

Implementation notes:
- All statements are spelled with the `inverse`/`functor` of the equivalence (`eqvTensorIso`,
  `eqvUnitIso`, `eqvUnitApp` are respellings of `pullbackTensorObjIso g`, `pullbackUnitIso g`,
  `unitIso.app A`); otherwise the types of the pieces of `Equiv.trans` agree only at default
  transparency and `simp`/`rw` cannot match.
- Goals containing `SheafOfModules.unit W.ringCatSheaf` (`W.ringCatSheaf : TopCat.Sheaf …` has to be
  unfolded to `Sheaf (Opens.grothendieckTopology …) …`) do not typecheck at implicit transparency:
  `rw`/`simp` with metavariables (`Category.assoc`, `Functor.map_comp`) fail on them, and only
  **closed-term** rewrites work; the same holds for goals containing `dualEv` (`dual V` versus
  `internalHom V O_X`). So the reassociation is done in the equation `h7`, which does not contain
  `O_W`, and the remaining steps use `Category.assoc` with explicit arguments. `congr 1` takes 30 s on
  such goals (`congrArg` is used instead).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {W T : AlgebraicGeometry.Scheme.{u}} (g : W ⟶ T) [IsIso g]

/-- The equivalence `W.Modules ≌ T.Modules` given by pullback along an isomorphism `g : W ≅ T`:
forward `(g⁻¹)^*`, inverse `g^*`, unit/counit from `pullbackComp`, `pullbackId` (`Equivalence.mk`
does not require the triangle identities). -/
def pullbackEquivalenceOfIsIso : W.Modules ≌ T.Modules :=
  CategoryTheory.Equivalence.mk (pullback (inv g)) (pullback g)
    ((pullbackId W).symm ≪≫ eqToIso (by rw [IsIso.hom_inv_id]) ≪≫ (pullbackComp g (inv g)).symm)
    (pullbackComp (inv g) g ≪≫ eqToIso (by rw [IsIso.inv_hom_id]) ≪≫ pullbackId T)

theorem dualCurry_symm_naturality_left {X : AlgebraicGeometry.Scheme.{u}} {F' F : X.Modules}
    (V : X.Modules) (a : F' ⟶ F) (ψ : F ⟶ dual V) :
    (dualCurry F' V).symm (a ≫ ψ) = (a ▷ V) ≫ (dualCurry F V).symm ψ := by
  rw [dualCurry_symm_apply, dualCurry_symm_apply, MonoidalCategory.comp_whiskerRight]
  -- the type of `dualEv` does not typecheck at implicit transparency (`dual V` versus `internalHom V O_X`), hence `erw`
  erw [Category.assoc]

/-- `pullbackTensorObjIso g`, spelled with the `inverse` of the equivalence. -/
def eqvTensorIso (M E : T.Modules) :
    (pullbackEquivalenceOfIsIso g).inverse.obj (M ⊗ E) ≅
      (pullbackEquivalenceOfIsIso g).inverse.obj M ⊗ (pullbackEquivalenceOfIsIso g).inverse.obj E :=
  pullbackTensorObjIso g M E

/-- `pullbackUnitIso g`, spelled with the `inverse` of the equivalence. -/
def eqvUnitIso :
    (pullbackEquivalenceOfIsIso g).inverse.obj (SheafOfModules.unit T.ringCatSheaf) ≅
      SheafOfModules.unit W.ringCatSheaf :=
  pullbackUnitIso g

/-- The unit of the equivalence `A ≅ g^*((g⁻¹)^*A)`, spelled as `inverse.obj (functor.obj A)`. -/
def eqvUnitApp (A : W.Modules) :
    A ≅ (pullbackEquivalenceOfIsIso g).inverse.obj ((pullbackEquivalenceOfIsIso g).functor.obj A) :=
  (pullbackEquivalenceOfIsIso g).unitIso.app A

theorem eqvTensorIso_inv_natural_left {M M' : T.Modules} (φ : M ⟶ M') (E : T.Modules) :
    (pullbackEquivalenceOfIsIso g).inverse.map φ ▷ (pullbackEquivalenceOfIsIso g).inverse.obj E ≫
        (eqvTensorIso g M' E).inv =
      (eqvTensorIso g M E).inv ≫ (pullbackEquivalenceOfIsIso g).inverse.map (φ ▷ E) :=
  pullback_μ_natural_left g φ E

theorem eqvUnitApp_hom_natural {A' A : W.Modules} (a : A' ⟶ A) :
    (eqvUnitApp g A').hom ≫ (pullbackEquivalenceOfIsIso g).inverse.map
        ((pullbackEquivalenceOfIsIso g).functor.map a) =
      a ≫ (eqvUnitApp g A).hom :=
  (pullbackEquivalenceOfIsIso g).unit_naturality a

/-- `Hom(A, g^*E^∨) ≃ Hom(A, (g^*E)^∨)`, natural in `A` (`dualPullbackHomEquiv_naturality`): adjoint
transpose → uncurry → `g^*` fully faithful → change of base through the monoidal isomorphisms `μ`,
`ε` and the equivalence unit `η` → curry. -/
def dualPullbackHomEquiv (E : T.Modules) (A : W.Modules) :
    (A ⟶ (pullbackEquivalenceOfIsIso g).inverse.obj (dual E)) ≃
      (A ⟶ dual ((pullbackEquivalenceOfIsIso g).inverse.obj E)) :=
  ((pullbackEquivalenceOfIsIso g).toAdjunction.homEquiv A (dual E)).symm.trans <|
  (dualCurry ((pullbackEquivalenceOfIsIso g).functor.obj A) E).symm.trans <|
  (pullbackEquivalenceOfIsIso g).fullyFaithfulInverse.homEquiv.trans <|
  (Iso.homCongr (eqvTensorIso g ((pullbackEquivalenceOfIsIso g).functor.obj A) E ≪≫
      MonoidalCategory.whiskerRightIso (eqvUnitApp g A).symm
        ((pullbackEquivalenceOfIsIso g).inverse.obj E)) (eqvUnitIso g)).trans <|
  dualCurry A ((pullbackEquivalenceOfIsIso g).inverse.obj E)

/-- The explicit formula for `dualPullbackHomEquiv` (unfolding the definition, `rfl`). -/
theorem dualPullbackHomEquiv_apply (E : T.Modules) (A : W.Modules)
    (f : A ⟶ (pullbackEquivalenceOfIsIso g).inverse.obj (dual E)) :
    dualPullbackHomEquiv g E A f =
      dualCurry A ((pullbackEquivalenceOfIsIso g).inverse.obj E)
        ((((eqvUnitApp g A).hom ▷ (pullbackEquivalenceOfIsIso g).inverse.obj E) ≫
            (eqvTensorIso g ((pullbackEquivalenceOfIsIso g).functor.obj A) E).inv) ≫
          (pullbackEquivalenceOfIsIso g).inverse.map
            ((dualCurry ((pullbackEquivalenceOfIsIso g).functor.obj A) E).symm
              (((pullbackEquivalenceOfIsIso g).toAdjunction.homEquiv A (dual E)).symm f)) ≫
          (eqvUnitIso g).hom) :=
  rfl

theorem dualPullbackHomEquiv_naturality (E : T.Modules) {A' A : W.Modules} (a : A' ⟶ A)
    (f : A ⟶ (pullbackEquivalenceOfIsIso g).inverse.obj (dual E)) :
    dualPullbackHomEquiv g E A' (a ≫ f) = a ≫ dualPullbackHomEquiv g E A f := by
  have h1 : ((pullbackEquivalenceOfIsIso g).toAdjunction.homEquiv A' (dual E)).symm (a ≫ f) =
      (pullbackEquivalenceOfIsIso g).functor.map a ≫
        ((pullbackEquivalenceOfIsIso g).toAdjunction.homEquiv A (dual E)).symm f :=
    Adjunction.homEquiv_naturality_left_symm _ _ _
  have h2 : (dualCurry ((pullbackEquivalenceOfIsIso g).functor.obj A') E).symm
        ((pullbackEquivalenceOfIsIso g).functor.map a ≫
          ((pullbackEquivalenceOfIsIso g).toAdjunction.homEquiv A (dual E)).symm f) =
      ((pullbackEquivalenceOfIsIso g).functor.map a ▷ E) ≫
        (dualCurry ((pullbackEquivalenceOfIsIso g).functor.obj A) E).symm
          (((pullbackEquivalenceOfIsIso g).toAdjunction.homEquiv A (dual E)).symm f) :=
    dualCurry_symm_naturality_left E _ _
  have h3 : (pullbackEquivalenceOfIsIso g).inverse.map
        (((pullbackEquivalenceOfIsIso g).functor.map a ▷ E) ≫
          (dualCurry ((pullbackEquivalenceOfIsIso g).functor.obj A) E).symm
            (((pullbackEquivalenceOfIsIso g).toAdjunction.homEquiv A (dual E)).symm f)) =
      (pullbackEquivalenceOfIsIso g).inverse.map ((pullbackEquivalenceOfIsIso g).functor.map a ▷ E) ≫
        (pullbackEquivalenceOfIsIso g).inverse.map
          ((dualCurry ((pullbackEquivalenceOfIsIso g).functor.obj A) E).symm
            (((pullbackEquivalenceOfIsIso g).toAdjunction.homEquiv A (dual E)).symm f)) :=
    Functor.map_comp _ _ _
  have h4 := eqvTensorIso_inv_natural_left g ((pullbackEquivalenceOfIsIso g).functor.map a) E
  have h5 := eqvUnitApp_hom_natural g a
  rw [dualPullbackHomEquiv_apply, dualPullbackHomEquiv_apply, h1, h2, h3, dualCurry_naturality_left]
  -- the part not involving the structure sheaf O_W (goals containing `SheafOfModules.unit W.ringCatSheaf`
  -- do not typecheck at implicit transparency, so `rw`/`simp` with metavariables fail on them; the
  -- reassociation is therefore done in this equation, which does not contain it)
  have h7 : ((eqvUnitApp g A').hom ▷ (pullbackEquivalenceOfIsIso g).inverse.obj E ≫
        (eqvTensorIso g ((pullbackEquivalenceOfIsIso g).functor.obj A') E).inv) ≫
        (pullbackEquivalenceOfIsIso g).inverse.map ((pullbackEquivalenceOfIsIso g).functor.map a ▷ E) =
      a ▷ (pullbackEquivalenceOfIsIso g).inverse.obj E ≫
        (eqvUnitApp g A).hom ▷ (pullbackEquivalenceOfIsIso g).inverse.obj E ≫
          (eqvTensorIso g ((pullbackEquivalenceOfIsIso g).functor.obj A) E).inv := by
    rw [Category.assoc, ← h4, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight, h5,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
  -- `congr 1` takes 30 s here (deep unfolding while trying rfl); use an explicit `congrArg` instead
  refine congrArg (dualCurry A' ((pullbackEquivalenceOfIsIso g).inverse.obj E)) ?_
  set f₂ := (dualCurry ((pullbackEquivalenceOfIsIso g).functor.obj A) E).symm
    (((pullbackEquivalenceOfIsIso g).toAdjunction.homEquiv A (dual E)).symm f) with hf₂
  rw [Category.assoc ((pullbackEquivalenceOfIsIso g).inverse.map
        ((pullbackEquivalenceOfIsIso g).functor.map a ▷ E))
      ((pullbackEquivalenceOfIsIso g).inverse.map f₂) (eqvUnitIso g).hom,
    Category.assoc ((eqvUnitApp g A').hom ▷ (pullbackEquivalenceOfIsIso g).inverse.obj E)
      (eqvTensorIso g ((pullbackEquivalenceOfIsIso g).functor.obj A') E).inv
      ((pullbackEquivalenceOfIsIso g).inverse.map ((pullbackEquivalenceOfIsIso g).functor.map a ▷ E) ≫
        (pullbackEquivalenceOfIsIso g).inverse.map f₂ ≫ (eqvUnitIso g).hom),
    (reassoc_of% h7) ((pullbackEquivalenceOfIsIso g).inverse.map f₂ ≫ (eqvUnitIso g).hom),
    Category.assoc ((eqvUnitApp g A).hom ▷ (pullbackEquivalenceOfIsIso g).inverse.obj E)
      (eqvTensorIso g ((pullbackEquivalenceOfIsIso g).functor.obj A) E).inv
      ((pullbackEquivalenceOfIsIso g).inverse.map f₂ ≫ (eqvUnitIso g).hom)]

end AlgebraicGeometry.Scheme.Modules

/-- The dual commutes with pullback along isomorphisms: for `g : W ⟶ T` an isomorphism,
`g^*(E^∨) ≅ (g^*E)^∨`. -/
theorem AlgebraicGeometry.Scheme.Modules.dual_pullback_of_isIso {W T : AlgebraicGeometry.Scheme.{u}}
    (g : W ⟶ T) [IsIso g] (E : T.Modules) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (AlgebraicGeometry.Scheme.Modules.dual E) ≅
      AlgebraicGeometry.Scheme.Modules.dual ((AlgebraicGeometry.Scheme.Modules.pullback g).obj E)) :=
  ⟨Yoneda.ext ((pullbackEquivalenceOfIsIso g).inverse.obj (dual E))
    (dual ((pullbackEquivalenceOfIsIso g).inverse.obj E))
    (fun {A} => dualPullbackHomEquiv g E A) (fun {A} => (dualPullbackHomEquiv g E A).symm)
    (fun f => Equiv.symm_apply_apply _ f) (fun f => Equiv.apply_symm_apply _ f)
    (fun a f => dualPullbackHomEquiv_naturality g E a f)⟩

end
