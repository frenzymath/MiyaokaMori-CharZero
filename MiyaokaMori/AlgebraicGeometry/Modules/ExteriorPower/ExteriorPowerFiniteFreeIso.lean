import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerFiniteFree
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Data.Set.PowersetCard

/-! # Exterior powers of a finite free sheaf of modules

The `n`-th exterior power of a finite free sheaf of modules of rank `r` is isomorphic to the free
sheaf of rank `C(r,n)`: `⋀^n (O_X^{⊕ r}) ≅ O_X^{⊕ C(r,n)}` (sheaf-level version;
`ExteriorPowerFiniteFree` gives only the case `n = r`).

Proof (local computation of Stacks 01CK + Mathlib's exterior power basis):
1. Openwise: `Γ(O^r, U)` has the standard basis `finiteFreeSectionBasis` (indexed by `Fin r`);
   Mathlib's `Module.Basis.exteriorPower` gives a basis of `⋀^n Γ(O^r, U)` indexed by
   `Set.powersetCard (Fin r) n` (the `n`-element subsets of `Fin r`), of cardinality `r.choose n`
   (`Set.powersetCard.card`). Via `Basis.equivFun` and reindexing,
   `⋀^n Γ(O^r,U) ≃ₗ (Fin C(r,n) → Γ(O,U)) ≃ₗ Γ(O^{C(r,n)}, U)`.
2. Compatibility with restriction: the coordinate of the wedge `v₁∧…∧vₙ` at a subset `s` is the minor
   of the coordinate matrix on the rows `s` (`exteriorPower.ιMultiDual_apply_ιMulti`); minors commute
   with ring homomorphisms (`RingHom.map_det`), and the coordinates of sections of the free sheaf
   commute with restriction (`finiteFreeSectionsIso_restrict`). This gives an isomorphism of presheaves.
3. Sheafification: `moduleExteriorPower` is the sheafification of the presheaf exterior power, the free
   sheaf is already a sheaf, and the counit of sheafification is an isomorphism.

Source: Stacks 01CK; Mathlib `LinearAlgebra/ExteriorPower/Basis.lean` (`Module.Basis.exteriorPower`,
`ιMultiDual_apply_ιMulti`); this generalizes `ExteriorPowerFiniteFree` (the case `n = r`).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace MiyaokaMori.ExteriorPowerFiniteFree

universe u

variable (X : Scheme.{u})

local instance sectionCommRingGen (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- There are `r.choose n` subsets of `Fin r` with `n` elements. -/
theorem card_powersetCard_fin (r n : ℕ) :
    Fintype.card (Set.powersetCard (Fin r) n) = r.choose n := by
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- An equivalence between the index set of the exterior power basis and `ULift (Fin (r.choose n))`
(lifting the index set to universe `u`). -/
def powersetCardIndexEquiv (r n : ℕ) :
    ULift.{u} (Fin (r.choose n)) ≃ Set.powersetCard (Fin r) n :=
  Equiv.ulift.trans (Fintype.equivFinOfCardEq (card_powersetCard_fin r n)).symm

/-- `finiteFreeSectionsIso_restrict` in `PresheafOfModules.map` form (coordinates commute with
restriction). -/
theorem finiteFreeSectionsIso_map (I : Type u) [Finite I] {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (x : (SheafOfModules.free (R := X.ringCatSheaf) I).val.obj U) (k : I) :
    (finiteFreeSectionsIso X I V.unop).hom.hom
        ((SheafOfModules.free (R := X.ringCatSheaf) I).val.map i x) k =
      X.ringCatSheaf.obj.map i ((finiteFreeSectionsIso X I U.unop).hom.hom x k) := by
  erw [finiteFreeSectionsIso_apply, finiteFreeSectionsIso_apply]
  exact PresheafOfModules.naturality_apply
    (((finiteFreeProductIso X I).hom ≫ Pi.π _ k).val) i x

/-- On sections: the coordinate equivalence of `⋀^n Γ(O^r, U)` (Mathlib exterior power basis +
reindexing). -/
def exteriorFiniteFreeCoordEquiv (r n : ℕ) (U : X.Opens) :
    (⋀[X.ringCatSheaf.obj.obj (op U)]^n
        ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.obj (op U)))
      ≃ₗ[X.ringCatSheaf.obj.obj (op U)]
      (ULift.{u} (Fin (r.choose n)) → X.ringCatSheaf.obj.obj (op U)) :=
  ((finiteFreeSectionBasis X r U).exteriorPower n).equivFun ≪≫ₗ
    LinearEquiv.funCongrLeft _ _ (powersetCardIndexEquiv.{u} r n)

/-- The coordinates of a wedge are the minors of the coordinate matrix (rows indexed by the subset `s`). -/
theorem exteriorFiniteFreeCoordEquiv_mk (r n : ℕ) (U : X.Opens)
    (v : Fin n → (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.obj (op U))
    (k : ULift.{u} (Fin (r.choose n))) :
    exteriorFiniteFreeCoordEquiv X r n U (ModuleCat.exteriorPower.mk v) k =
      (Matrix.of fun i j : Fin n ↦
        (finiteFreeSectionsIso X (ULift.{u} (Fin r)) U).hom.hom (v i)
          (ULift.up (Set.powersetCard.ofFinEmbEquiv.symm
            (powersetCardIndexEquiv.{u} r n k) j))).det := by
  change ((finiteFreeSectionBasis X r U).exteriorPower n).equivFun
    (exteriorPower.ιMulti _ n v) (powersetCardIndexEquiv.{u} r n k) = _
  rw [Module.Basis.equivFun_apply, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1

/-- The linear equivalence on sections `⋀^n Γ(O^r, U) ≃ₗ Γ(O^{C(r,n)}, U)`. -/
def exteriorFiniteFreeSectionsEquivGen (r n : ℕ) (U : X.Opens) :
    (⋀[X.ringCatSheaf.obj.obj (op U)]^n
        ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.obj (op U)))
      ≃ₗ[X.ringCatSheaf.obj.obj (op U)]
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r.choose n)))).val.obj (op U) :=
  exteriorFiniteFreeCoordEquiv X r n U ≪≫ₗ
    (finiteFreeSectionsIso X (ULift.{u} (Fin (r.choose n))) U).toLinearEquiv.symm

theorem finiteFreeSectionsIso_exteriorFiniteFreeSectionsEquivGen (r n : ℕ) (U : X.Opens)
    (y : ⋀[X.ringCatSheaf.obj.obj (op U)]^n
        ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.obj (op U))) :
    (finiteFreeSectionsIso X (ULift.{u} (Fin (r.choose n))) U).hom.hom
        (exteriorFiniteFreeSectionsEquivGen X r n U y) =
      exteriorFiniteFreeCoordEquiv X r n U y :=
  (finiteFreeSectionsIso X (ULift.{u} (Fin (r.choose n))) U).toLinearEquiv.apply_symm_apply _

/-- The isomorphism on sections `⋀^n Γ(O^r, U) ≅ Γ(O^{C(r,n)}, U)`. -/
def exteriorFiniteFreeSectionsIsoGen (r n : ℕ) (U : X.Opens) :
    ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.obj (op U)).exteriorPower n ≅
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r.choose n)))).val.obj (op U) :=
  (exteriorFiniteFreeSectionsEquivGen X r n U).toModuleIso

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The coordinate equivalence is compatible with restriction (abstract form): if the coordinates of
`w` are the restrictions along `i` of those of `v`, then the wedge coordinates of `w` are the
restrictions of those of `v` (minors commute with ring homomorphisms). -/
theorem exteriorFiniteFreeCoordEquiv_compat (r n : ℕ) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (v : Fin n → (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.obj (op U.unop))
    (w : Fin n → (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.obj (op V.unop))
    (hw : ∀ (a : Fin n) (m : ULift.{u} (Fin r)),
      (finiteFreeSectionsIso X (ULift.{u} (Fin r)) V.unop).hom.hom (w a) m =
        X.ringCatSheaf.obj.map i ((finiteFreeSectionsIso X (ULift.{u} (Fin r)) U.unop).hom.hom (v a) m))
    (k : ULift.{u} (Fin (r.choose n))) :
    exteriorFiniteFreeCoordEquiv X r n V.unop (ModuleCat.exteriorPower.mk w) k =
      X.ringCatSheaf.obj.map i
        (exteriorFiniteFreeCoordEquiv X r n U.unop (ModuleCat.exteriorPower.mk v) k) := by
  rw [exteriorFiniteFreeCoordEquiv_mk, exteriorFiniteFreeCoordEquiv_mk]
  erw [(X.ringCatSheaf.obj.map i).hom.map_det]
  congr 1
  ext a b
  exact hw a _

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the presheaf isomorphism: the section isomorphisms commute with restriction. -/
theorem exteriorFiniteFreeSectionsEquivGen_naturality (r n : ℕ) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (v : Fin n → (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val.obj U) :
    exteriorFiniteFreeSectionsEquivGen X r n V.unop
        (AlgebraicGeometry.Scheme.Modules.exteriorRestriction X
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val n i
          (ModuleCat.exteriorPower.mk v)) =
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r.choose n)))).val.map i
        (exteriorFiniteFreeSectionsEquivGen X r n U.unop (ModuleCat.exteriorPower.mk v)) := by
  apply (finiteFreeSectionsIso X (ULift.{u} (Fin (r.choose n))) V.unop).toLinearEquiv.injective
  funext k
  refine Eq.trans ?_ (finiteFreeSectionsIso_map X (ULift.{u} (Fin (r.choose n))) i _ k).symm
  refine Eq.trans ?_ (congrArg (X.ringCatSheaf.obj.map i) (congrFun
    (finiteFreeSectionsIso_exteriorFiniteFreeSectionsEquivGen X r n U.unop
      (ModuleCat.exteriorPower.mk v)) k)).symm
  refine Eq.trans (congrFun (finiteFreeSectionsIso_exteriorFiniteFreeSectionsEquivGen X r n V.unop _) k) ?_
  refine Eq.trans (congrArg (fun y => exteriorFiniteFreeCoordEquiv X r n V.unop y k)
    (AlgebraicGeometry.Scheme.Modules.exteriorRestriction_mk X
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val n i v)) ?_
  exact exteriorFiniteFreeCoordEquiv_compat X r n i v _
    (fun a m => finiteFreeSectionsIso_map X (ULift.{u} (Fin r)) i (v a) m) k

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf isomorphism `⋀^n_{pre}(O^r) ≅ O^{C(r,n)}` (compatible with restriction: minors commute
with ring homomorphisms). -/
def exteriorFiniteFreePresheafIsoGen (r n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.moduleExteriorPresheaf X
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))).val n ≅
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r.choose n)))).val :=
  PresheafOfModules.isoMk (fun U ↦ exteriorFiniteFreeSectionsIsoGen X r n U.unop) (by
    intro U V i
    apply ModuleCat.exteriorPower.hom_ext
    ext v
    exact exteriorFiniteFreeSectionsEquivGen_naturality X r n i v)

/-- The isomorphism of sheaves `⋀^n (O_X^{⊕ r}) ≅ O_X^{⊕ C(r,n)}`. -/
def moduleExteriorPowerFiniteFreeIsoGen (r n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) n ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r.choose n))) :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (exteriorFiniteFreePresheafIsoGen X r n) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r.choose n))))

end MiyaokaMori.ExteriorPowerFiniteFree
