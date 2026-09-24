import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseAwayMapBijective
import MiyaokaMori.RingTheory.SymmetricAlgebraSplitPolynomialModel
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraSectionsRingEquivSym
import MiyaokaMori.AlgebraicGeometry.Modules.DualMapAdditiveBiproduct
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiprodLocallyFree

/-! # The graded model `A(W) ≅ Sym(L^∨)(W)[T]` for `Tot(L) ⊆ P(O ⊕ L)`

Shared core of the three leaves of `TotLineAffineOverBase` (Stacks 01NS, 01O4). Notation: `V = O ⊕ L`, `W ⊆ X`
affine, `R = Γ(W, O)`, `M = Γ(W, V^∨)`, `N = Γ(W, L^∨)`, `A(W) = ⊕_m Γ(W, Sym^m V^∨)` (graded by `sectionsGrading`),
`p : Tot(L) = Spec_X Sym(L^∨) → X`. Everything is stated for an arbitrary isomorphism `ε : O^∨ ≅ O` (in the main
file `ε = (dualUnitEval, unitDualSection)`; that module's names cannot be used here because
`TotLineAffineOverBaseDefs` declares the same names) and, in §4, for an arbitrary ring homomorphism
`f : A(W) → Γ(p⁻¹W, O)` with prescribed values on the generators (in the main file `f = φ_W`, the canonical local
piece of `toProjBundle`).

1. **Splitting** (`sectionsSplitting`): `M = R·T ⊕ N` with `T = oFunctional ε W = (fst)^∨(ε⁻¹ 1)` (so that
   `oCoordinate L W = symGen T`), `pr = ε ∘ (inl)^∨`, `q = (inr)^∨`, `s = (snd)^∨` (`ModulesDualCurryMap`;
   `dualMap_add` + `biprod.total` for `m = pr m • T + s (q m)`). Hence, by `SymmetricAlgebra.ModuleSplitting`
   (`TotLineAffineOverBaseSymPolynomialModel`) and `symGradedAlgebra.symLiftHom_bijective` (`A(W) ≅ Sym_R M`),
   `A(W) ≅ Sym_R N [X]` as graded rings.
2. **Functions on `Tot(L)|_W`** (`symSectionsToFunctions`): `Sym_R N ≅ Γ(W, Sym(L^∨)) ≅ Γ(p⁻¹W, O_Tot)`
   (`symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction`, `relativeSpec.sectionsIso`, `Opens.topIso`).
3. **The normalized piece** `φ_can = normalizedPiece = symSectionsToFunctions ∘ evalOne ∘ symLiftHom⁻¹ : A(W) → Γ(p⁻¹W, O)`
   ("set `T = 1`"): surjective, `φ_can(T) = 1`, injective on every homogeneous piece.
4. **Any `f : A(W) → Γ(p⁻¹W, O)` with `f(sectionsUnit r) = φ_can(r)`, `f(T) = u`, `f(ι(s n)) = u · φ_can(ι n)`** satisfies
   `f = u^k · φ_can` on `A(W)_k` (`eq_pow_mul_normalizedPiece_of_generators`), hence — if `u` is a unit — its
   degree-zero fraction map `(A(W)_T)_0 → Γ(p⁻¹W, O)[1/u]` is bijective (`awayMap_bijective_of_generator_values`,
   from `Proj.awayMapOfGlobalSections_bijective_of_unit_scaling`, `TotLineAffineOverBaseAwayMapBijective`).
   The main file applies this to `φ_W` (`toProjBundle_awayMap_bijective`), with the generator values
   `localRingHom_oCoordinate_isUnit`, `canonicalPiece_sectionsUnitHom`, `canonicalPiece_genSections_sLinear`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.totalSpace

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

attribute [local instance] AlgebraicGeometry.Scheme.Modules.symGradedAlgebra.sectionsAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)

/-! ## The splitting `Γ(W, (O ⊕ L)^∨) = R·T ⊕ Γ(W, L^∨)` -/

section Splitting

variable (ε : dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ≅
  (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

/-- The `O`-coordinate functional `T ∈ Γ(W, (O ⊕ L)^∨)`, `(a, l) ↦ a`: `(fst)^∨` applied to the section `ε⁻¹(1)` of
`O^∨` (for `ε⁻¹ = unitDualSection` this is the functional whose `symGen` is `oCoordinate L W`). -/
def oFunctional (W : X.Opens) :
    Γ(dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L), W) :=
  (dualCurryMap (biprod.fst (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
    (Y := L))).app W (ε.inv.app W (show Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, W) from
      (1 : Γ(X, W))))

/-- `pr : Γ(W, (O ⊕ L)^∨) → Γ(W, O)`, the `O`-component `φ ↦ ε(φ ∘ inl)`. -/
def prLinear (W : X.Opens) :
    Γ(dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L), W) →ₗ[Γ(X, W)]
      Γ(X, W) where
  toFun m := show Γ(X, W) from (dualCurryMap (biprod.inl (C := X.Modules)
    (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫ ε.hom).app W m
  map_add' m m' := map_add _ m m'
  map_smul' r m := Hom.app_smul _ r m

/-- `q : Γ(W, (O ⊕ L)^∨) → Γ(W, L^∨)`, restriction along `inr`. -/
def qLinear (W : X.Opens) :
    Γ(dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L), W) →ₗ[Γ(X, W)]
      Γ(dual L, W) where
  toFun m := (dualCurryMap (biprod.inr (C := X.Modules)
    (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))).app W m
  map_add' m m' := map_add _ m m'
  map_smul' r m := Hom.app_smul _ r m

/-- `s : Γ(W, L^∨) → Γ(W, (O ⊕ L)^∨)`, composition with `snd`. -/
def sLinear (W : X.Opens) :
    Γ(dual L, W) →ₗ[Γ(X, W)]
      Γ(dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L), W) where
  toFun n := (dualCurryMap (biprod.snd (C := X.Modules)
    (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))).app W n
  map_add' n n' := map_add _ n n'
  map_smul' r n := Hom.app_smul _ r n

theorem sLinear_apply (W : X.Opens) (n : Γ(dual L, W)) :
    sLinear L W n = (dualCurryMap (biprod.snd (C := X.Modules)
      (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))).app W n := rfl

/-- `(inl)^∨ ≫ (fst)^∨ + (inr)^∨ ≫ (snd)^∨ = 𝟙 (O ⊕ L)^∨` (`biprod.total` dualized; `dualMap_add`). -/
theorem dualCurryMap_biprod_total :
    dualCurryMap (biprod.inl (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
        dualCurryMap (biprod.fst (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) +
      dualCurryMap (biprod.inr (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
        dualCurryMap (biprod.snd (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) =
      𝟙 (dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)) := by
  have h := congrArg dualMap (biprod.total (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))
  rw [dualMap_add, dualMap_comp, dualMap_comp, dualMap_id] at h
  exact h

omit L in
/-- A section of `O^∨` is `ε(x)` times the section `ε⁻¹(1)`: `x = ε x • ε⁻¹ 1`. -/
theorem eq_smul_inv_one (W : X.Opens) (x : Γ(dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf), W)) :
    x = (show Γ(X, W) from ε.hom.app W x) •
      ε.inv.app W (show Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, W) from (1 : Γ(X, W))) := by
  have h : ε.inv.app W (ε.hom.app W x) = x := congrArg (fun k => k.app W x) ε.hom_inv_id
  rw [← Hom.app_smul]
  refine h.symm.trans (congrArg (ε.inv.app W) ?_)
  show ε.hom.app W x = (show Γ(X, W) from ε.hom.app W x) * (1 : Γ(X, W))
  exact (mul_one (show Γ(X, W) from ε.hom.app W x)).symm

/-- **`Γ(W, (O ⊕ L)^∨) = R·T ⊕ Γ(W, L^∨)`**: the splitting data of `SymmetricAlgebra.ModuleSplitting`. -/
def sectionsSplitting (W : X.Opens) :
    SymmetricAlgebra.ModuleSplitting Γ(X, W)
      Γ(dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L), W)
      Γ(dual L, W) where
  pr := prLinear L ε W
  q := qLinear L W
  T := oFunctional L ε W
  s := sLinear L W
  pr_T := by
    show (show Γ(X, W) from (dualCurryMap biprod.inl ≫ ε.hom).app W ((dualCurryMap biprod.fst).app W
      (ε.inv.app W (show Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, W) from (1 : Γ(X, W)))))) = 1
    have h := congrArg (fun k => k.app W (show Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, W) from
      (1 : Γ(X, W)))) (show ε.inv ≫ dualCurryMap (biprod.fst (C := X.Modules)
        (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L)) ≫
        (dualCurryMap biprod.inl ≫ ε.hom) = 𝟙 _ by
      rw [← Category.assoc (dualCurryMap _), dualCurryMap_fst_comp_inl, Category.id_comp, Iso.inv_hom_id])
    exact h
  q_T := by
    show (dualCurryMap biprod.inr).app W ((dualCurryMap biprod.fst).app W
      (ε.inv.app W (show Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, W) from (1 : Γ(X, W))))) = 0
    have h := congrArg (fun k => k.app W (ε.inv.app W (show Γ(show X.Modules from SheafOfModules.unit X.ringCatSheaf, W)
      from (1 : Γ(X, W))))) (dualCurryMap_fst_comp_inr (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
    exact h
  q_s n := by
    have h := congrArg (fun k => k.app W n)
      (dualCurryMap_snd_comp_inr (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
    exact h
  pr_s n := by
    show (show Γ(X, W) from (dualCurryMap biprod.inl ≫ ε.hom).app W ((dualCurryMap biprod.snd).app W n)) = 0
    have h := congrArg (fun k => k.app W n)
      (show dualCurryMap (biprod.snd (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
        (Y := L)) ≫ (dualCurryMap biprod.inl ≫ ε.hom) = 0 by
        rw [← Category.assoc, dualCurryMap_snd_comp_inl, zero_comp])
    exact h
  eq_smul_add m := by
    have h : (dualCurryMap (biprod.fst (C := X.Modules)
          (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))).app W
          ((dualCurryMap (biprod.inl (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))).app W m) +
        (dualCurryMap (biprod.snd (C := X.Modules)
          (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))).app W
          ((dualCurryMap (biprod.inr (C := X.Modules)
            (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))).app W m) = m :=
      congrArg (fun k => k.app W m) (dualCurryMap_biprod_total L)
    rw [eq_smul_inv_one ε W ((dualCurryMap (biprod.inl (C := X.Modules)
      (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf) (Y := L))).app W m), Hom.app_smul] at h
    exact h.symm

end Splitting

/-! ## Functions on `Tot(L)|_W`: `Sym_R Γ(W, L^∨) ≅ Γ(p⁻¹W, O_Tot)` -/

variable [L.IsLineBundle]

theorem dual_isQuasicoherent : (dual L).IsQuasicoherent :=
  have := isLocallyFree_dual' L
  isQuasicoherent_of_isLocallyFree _

theorem dual_biprod_isQuasicoherent :
    (dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).IsQuasicoherent :=
  have := isLocallyFree_dual' (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
  isQuasicoherent_of_isLocallyFree _

/-- **The symmetric algebra of `Γ(W, L^∨)` as functions on `Tot(L)|_W = p⁻¹W`**:
`Sym_R Γ(W, L^∨) ≅ Γ(W, Sym(L^∨)) = Γ(p⁻¹W, O_Tot)` (`symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction`,
`relativeSpec.sectionsIso`, `Opens.topIso`); `ι n ↦` the fibre coordinate of `n`, `algebraMap r ↦ p^♯ r`. -/
def symSectionsToFunctions (W : X.affineOpens) :
    SymmetricAlgebra Γ(X, W.1) Γ(dual L, W.1) →+* Γ(((totalSpace L).hom ⁻¹ᵁ W.1).toScheme, ⊤) :=
  letI := ((symGradedAlgebra (dual L)).total.sectionsUnit W.1).toAlgebra
  haveI := dual_isQuasicoherent L
  ((((totalSpace L).hom ⁻¹ᵁ W.1).topIso.inv.hom.comp
      (relativeSpec.sectionsIso (symGradedAlgebra (dual L)).total W).hom.hom).comp
    (symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction (dual L) W).equiv.toRingEquiv.toRingHom)

theorem symSectionsToFunctions_bijective (W : X.affineOpens) :
    Function.Bijective (symSectionsToFunctions L W) := by
  letI := ((symGradedAlgebra (dual L)).total.sectionsUnit W.1).toAlgebra
  haveI := dual_isQuasicoherent L
  have h1 : Function.Bijective (relativeSpec.sectionsIso (symGradedAlgebra (dual L)).total W).hom.hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp (Iso.isIso_hom _)
  have h2 : Function.Bijective ((totalSpace L).hom ⁻¹ᵁ W.1).topIso.inv.hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp (Iso.isIso_inv _)
  exact (h2.comp h1).comp
    (symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction (dual L) W).equiv.toRingEquiv.bijective

/-- `symSectionsToFunctions (ι n)` is the fibre coordinate of `n`: the section `structureHom (totalIncl 1 (symGen n))`
of `O_Tot` over `p⁻¹W`, read on the open subscheme `p⁻¹W`. -/
theorem symSectionsToFunctions_ι (W : X.affineOpens) (n : Γ(dual L, W.1)) :
    symSectionsToFunctions L W (SymmetricAlgebra.ι Γ(X, W.1) Γ(dual L, W.1) n) =
      ((totalSpace L).hom ⁻¹ᵁ W.1).topIso.inv.hom
        ((relativeSpec.structureHom (symGradedAlgebra (dual L)).total).app W.1
          ((symGen (dual L) ≫ (symGradedAlgebra (dual L)).totalIncl 1).app W.1 n)) := by
  letI := ((symGradedAlgebra (dual L)).total.sectionsUnit W.1).toAlgebra
  haveI := dual_isQuasicoherent L
  rw [relativeSpec.structureHom_app_affine]
  show ((totalSpace L).hom ⁻¹ᵁ W.1).topIso.inv.hom ((relativeSpec.sectionsIso _ W).hom.hom
    ((symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction (dual L) W).equiv
      (SymmetricAlgebra.ι Γ(X, W.1) Γ(dual L, W.1) n))) = _
  rw [IsSymmetricAlgebra.equiv_apply, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- `symSectionsToFunctions (algebraMap r)` is the structure-map value `structureHom (sectionsUnit r)` (`= p^♯ r`). -/
theorem symSectionsToFunctions_algebraMap (W : X.affineOpens) (r : Γ(X, W.1)) :
    symSectionsToFunctions L W (algebraMap Γ(X, W.1) _ r) =
      ((totalSpace L).hom ⁻¹ᵁ W.1).topIso.inv.hom
        ((relativeSpec.structureHom (symGradedAlgebra (dual L)).total).app W.1
          ((symGradedAlgebra (dual L)).total.sectionsUnit W.1 r)) := by
  letI := ((symGradedAlgebra (dual L)).total.sectionsUnit W.1).toAlgebra
  haveI := dual_isQuasicoherent L
  rw [relativeSpec.structureHom_app_affine]
  show ((totalSpace L).hom ⁻¹ᵁ W.1).topIso.inv.hom ((relativeSpec.sectionsIso _ W).hom.hom
    ((symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction (dual L) W).equiv
      (algebraMap Γ(X, W.1) _ r))) = _
  rw [AlgEquiv.commutes]
  rfl

/-! ## The normalized piece `φ_can` -/

/-- `A(W) ≅ Sym_R Γ(W, (O ⊕ L)^∨)` (`symGradedAlgebra.symLiftHom_bijective`). -/
def sectionsRingEquivSym (W : X.affineOpens) :
    SymmetricAlgebra Γ(X, W.1) Γ(dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L), W.1) ≃+*
      (symGradedAlgebra (dual (biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsRing W.1 :=
  haveI := dual_biprod_isQuasicoherent L
  RingEquiv.ofBijective (symGradedAlgebra.symLiftHom _ W.1) (symGradedAlgebra.symLiftHom_bijective _ W.2)

theorem sectionsRingEquivSym_apply (W : X.affineOpens) (b) :
    sectionsRingEquivSym L W b = symGradedAlgebra.symLiftHom _ W.1 b := rfl

variable (ε : dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ≅
  (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

/-- **The normalized piece** `φ_can = symSectionsToFunctions ∘ evalOne ∘ symLiftHom⁻¹ : A(W) → Γ(p⁻¹W, O)`: "set
`T = 1`" (`T = oFunctional ε W`). -/
def normalizedPiece (W : X.affineOpens) :
    (symGradedAlgebra (dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsRing W.1 →+*
      Γ(((totalSpace L).hom ⁻¹ᵁ W.1).toScheme, ⊤) :=
  ((symSectionsToFunctions L W).comp (sectionsSplitting L ε W.1).evalOne).comp
    (sectionsRingEquivSym L W).symm.toRingHom

theorem normalizedPiece_symLiftHom (W : X.affineOpens) (b) :
    normalizedPiece L ε W (symGradedAlgebra.symLiftHom _ W.1 b) =
      symSectionsToFunctions L W ((sectionsSplitting L ε W.1).evalOne b) := by
  show symSectionsToFunctions L W ((sectionsSplitting L ε W.1).evalOne
    ((sectionsRingEquivSym L W).symm (sectionsRingEquivSym L W b))) = _
  rw [RingEquiv.symm_apply_apply]

theorem normalizedPiece_sectionsUnitHom (W : X.affineOpens) (r : Γ(X, W.1)) :
    normalizedPiece L ε W ((symGradedAlgebra (dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsUnitHom W.1 r) =
      symSectionsToFunctions L W (algebraMap Γ(X, W.1) _ r) := by
  rw [← symGradedAlgebra.symLiftHom_algebraMap, normalizedPiece_symLiftHom,
    SymmetricAlgebra.ModuleSplitting.evalOne_algebraMap]

theorem normalizedPiece_genSections (W : X.affineOpens)
    (m : Γ(dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L), W.1)) :
    normalizedPiece L ε W (symGradedAlgebra.genSections _ W.1 m) =
      symSectionsToFunctions L W ((sectionsSplitting L ε W.1).evalOne (SymmetricAlgebra.ι Γ(X, W.1) _ m)) := by
  rw [← symGradedAlgebra.symLiftHom_ι, normalizedPiece_symLiftHom]

theorem normalizedPiece_genSections_oFunctional (W : X.affineOpens) :
    normalizedPiece L ε W (symGradedAlgebra.genSections _ W.1 (oFunctional L ε W.1)) = 1 := by
  rw [normalizedPiece_genSections]
  exact ((sectionsSplitting L ε W.1).evalOne_ι_T).symm ▸ map_one _

theorem normalizedPiece_genSections_sLinear (W : X.affineOpens) (n : Γ(dual L, W.1)) :
    normalizedPiece L ε W (symGradedAlgebra.genSections _ W.1 (sLinear L W.1 n)) =
      symSectionsToFunctions L W (SymmetricAlgebra.ι Γ(X, W.1) Γ(dual L, W.1) n) := by
  rw [normalizedPiece_genSections]
  exact congrArg _ ((sectionsSplitting L ε W.1).evalOne_ι_s n)

theorem normalizedPiece_surjective (W : X.affineOpens) : Function.Surjective (normalizedPiece L ε W) := by
  intro y
  obtain ⟨c, rfl⟩ := (symSectionsToFunctions_bijective L W).2 y
  obtain ⟨b, rfl⟩ := (sectionsSplitting L ε W.1).evalOne_surjective c
  exact ⟨symGradedAlgebra.symLiftHom _ W.1 b, normalizedPiece_symLiftHom L ε W b⟩

theorem normalizedPiece_eq_zero (W : X.affineOpens) (k : ℕ)
    (a : (symGradedAlgebra (dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsRing W.1)
    (ha : a ∈ (symGradedAlgebra (dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsGrading W.1 k)
    (h : normalizedPiece L ε W a = 0) : a = 0 := by
  haveI := dual_biprod_isQuasicoherent L
  obtain ⟨b, rfl⟩ := (sectionsRingEquivSym L W).surjective a
  rw [sectionsRingEquivSym_apply] at ha h ⊢
  rw [normalizedPiece_symLiftHom] at h
  rw [symGradedAlgebra.symLiftHom_mem_sectionsGrading_iff _ W.1 (symGradedAlgebra.symLiftHom_bijective _ W.2).1] at ha
  have hb : b = 0 := (sectionsSplitting L ε W.1).eq_zero_of_mem_symmetricPiece_of_evalOne_eq_zero ha
    ((symSectionsToFunctions_bijective L W).1 (h.trans (map_zero _).symm))
  rw [hb, map_zero]

/-! ## Ring homomorphisms out of `A(W)` prescribed on the generators -/

variable (W : X.affineOpens)
  (f : (symGradedAlgebra (dual (biprod (C := X.Modules)
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsRing W.1 →+*
    Γ(((totalSpace L).hom ⁻¹ᵁ W.1).toScheme, ⊤))
  {u : Γ(((totalSpace L).hom ⁻¹ᵁ W.1).toScheme, ⊤)}
  (hT : f (symGradedAlgebra.genSections _ W.1 (oFunctional L ε W.1)) = u)
  (h0 : ∀ r : Γ(X, W.1), f ((symGradedAlgebra (dual (biprod (C := X.Modules)
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsUnitHom W.1 r) =
    symSectionsToFunctions L W (algebraMap Γ(X, W.1) _ r))
  (h1 : ∀ n : Γ(dual L, W.1), f (symGradedAlgebra.genSections _ W.1 (sLinear L W.1 n)) =
    u * symSectionsToFunctions L W (SymmetricAlgebra.ι Γ(X, W.1) Γ(dual L, W.1) n))

include hT h0 h1 in
/-- `f` on all degree-one generators: `f(ι m) = u · φ_can(ι m)` (from the splitting `m = pr m • T + s (q m)`). -/
theorem map_genSections_eq_mul_normalizedPiece
    (m : Γ(dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L), W.1)) :
    f (symGradedAlgebra.genSections _ W.1 m) = u * normalizedPiece L ε W (symGradedAlgebra.genSections _ W.1 m) := by
  rw [normalizedPiece_genSections, SymmetricAlgebra.ModuleSplitting.evalOne_ι, map_add, mul_add]
  conv_lhs => rw [(sectionsSplitting L ε W.1).eq_smul_add m]
  rw [symGradedAlgebra.genSections_add, symGradedAlgebra.genSections_smul, symGradedAlgebra.smul_def', map_add,
    map_mul]
  show f (_) * f (symGradedAlgebra.genSections _ W.1 (oFunctional L ε W.1)) +
    f (symGradedAlgebra.genSections _ W.1 (sLinear L W.1 ((sectionsSplitting L ε W.1).q m))) = _
  rw [hT, h0, h1]
  ring

include hT h0 h1 in
/-- **`f = u^k · φ_can` on `A(W)_k`.** -/
theorem eq_pow_mul_normalizedPiece_of_generators (k : ℕ)
    (a : (symGradedAlgebra (dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsRing W.1)
    (ha : a ∈ (symGradedAlgebra (dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsGrading W.1 k) :
    f a = u ^ k * normalizedPiece L ε W a := by
  haveI := dual_biprod_isQuasicoherent L
  obtain ⟨b, rfl⟩ := (sectionsRingEquivSym L W).surjective a
  rw [sectionsRingEquivSym_apply] at ha ⊢
  rw [symGradedAlgebra.symLiftHom_mem_sectionsGrading_iff _ W.1 (symGradedAlgebra.symLiftHom_bijective _ W.2).1] at ha
  change b ∈ (LinearMap.range (SymmetricAlgebra.ι Γ(X, W.1) _)) ^ k at ha
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [symGradedAlgebra.symLiftHom_algebraMap, h0, normalizedPiece_sectionsUnitHom, pow_zero, one_mul]
  | add x y i _ _ hx hy =>
    rw [map_add, map_add, hx, hy, map_add (normalizedPiece L ε W), mul_add]
  | mem_mul m hm i x _ hx =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, map_mul, hx, symGradedAlgebra.symLiftHom_ι,
      map_genSections_eq_mul_normalizedPiece L ε W f hT h0 h1, map_mul (normalizedPiece L ε W)]
    simp only [Nat.succ_eq_add_one, pow_succ]
    ring

include hT h0 h1 in
/-- **The degree-zero fraction map of `f` is bijective** when `u = f(T)` is a unit
(`Proj.awayMapOfGlobalSections_bijective_of_unit_scaling` with the normalized piece `φ_can`). -/
theorem awayMap_bijective_of_generator_values (hu : IsUnit u) :
    Function.Bijective (AlgebraicGeometry.Proj.awayMapOfGlobalSections
      ((symGradedAlgebra (dual (biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsGrading W.1)
      f (symGradedAlgebra.genSections _ W.1 (oFunctional L ε W.1))) :=
  AlgebraicGeometry.Proj.awayMapOfGlobalSections_bijective_of_unit_scaling _ f ⟨_, rfl⟩
    (normalizedPiece L ε W) hu hT (normalizedPiece_genSections_oFunctional L ε W)
    (eq_pow_mul_normalizedPiece_of_generators L ε W f hT h0 h1) (normalizedPiece_surjective L ε W)
    (normalizedPiece_eq_zero L ε W)

end AlgebraicGeometry.Scheme.totalSpace

end
