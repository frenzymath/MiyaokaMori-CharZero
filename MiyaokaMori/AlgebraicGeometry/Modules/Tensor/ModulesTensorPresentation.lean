import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPreservesColimits
import MiyaokaMori.AlgebraicGeometry.Modules.FreeTensorFreeIso

/-! # A global presentation of a tensor product

**A global presentation of `M ⊗ N` from global presentations of `M` and `N`** (the algebraic core of
Stacks 01CE):

if `free ιM --rM--> free σM --πM--> M → 0` and `free ιN --rN--> free σN --πN--> N → 0` are exact,
then `free (σM × ιN) ⊕ free (ιM × σN) ⟶ free (σM × σN) --πM ⊗ πN--> M ⊗ N → 0` is exact.

The proof has two steps, both using only that `⊗` is right exact:

1. `A ⊗ (-)` sends the cokernel presentation `B ↠ N` to `A ⊗ B ↠ A ⊗ N` (`tensorLeftCokernel`);
   `(-) ⊗ N` sends the cokernel presentation `A ↠ M` to `A ⊗ N ↠ M ⊗ N` (`tensorRightCokernel`).
2. **Composite cokernel criterion** `CokernelComp.isColimitConj` (the general lemma of this file): if
   `p` is a cokernel of `u`, `q` a cokernel of `v`, `e` an epimorphism and `w ≫ p = e ≫ v`, then
   `p ≫ q` is a cokernel of `coprod.desc u w`. Here `e = free ιM ◁ πN` (an epimorphism since `⊗`
   preserves epimorphisms), `w = rM ▷ free σN`, and `w ≫ p = e ≫ v` is `whisker_exchange`.

Finally `freeTensorFreeIso` (`free I ⊗ free J ≅ free (I × J)`) and Mathlib's `freeSumIso`
(`free I ⨿ free J ≅ free (I ⊕ J)`) replace both ends by free sheaves, and Mathlib's
`SheafOfModules.presentationOfIsCokernelFree` concludes.

Used for the quasi-coherence of tensor products (Stacks 01CE, `isQuasicoherent_tensor`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.CokernelComp

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasBinaryCoproducts C]
  {D E F G Cc C' S E' : C}
  {u : D ⟶ E} {p : E ⟶ F} {hup : u ≫ p = 0}
  {v : Cc ⟶ F} {q : F ⟶ G} {hvq : v ≫ q = 0}
  {e : C' ⟶ Cc} {w : C' ⟶ E}

/-- `coprod.desc u w ≫ (p ≫ q) = 0`. -/
theorem desc_comp_eq_zero (hup : u ≫ p = 0) (hvq : v ≫ q = 0) (hw : w ≫ p = e ≫ v) :
    coprod.desc u w ≫ (p ≫ q) = 0 := by
  refine coprod.hom_ext ?_ ?_
  · rw [coprod.inl_desc_assoc, ← Category.assoc, hup, zero_comp, comp_zero]
  · rw [coprod.inr_desc_assoc, ← Category.assoc, hw, Category.assoc, hvq, comp_zero, comp_zero]

theorem conj_comp_eq_zero (hup : u ≫ p = 0) (hvq : v ≫ q = 0) (hw : w ≫ p = e ≫ v)
    (α : S ≅ D ⨿ C') (β : E' ≅ E) :
    (α.hom ≫ coprod.desc u w ≫ β.inv) ≫ (β.hom ≫ p ≫ q) = 0 := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    desc_comp_eq_zero hup hvq hw, comp_zero]

/-- **Composite cokernel criterion**: if `p` is a cokernel of `u`, `q` a cokernel of `v`, `e` an
epimorphism and `w ≫ p = e ≫ v`, then `p ≫ q` is a cokernel of `coprod.desc u w`; conjugated along
the isomorphisms `α`, `β`. -/
def isColimitConj (hp : IsColimit (CokernelCofork.ofπ p hup))
    (hq : IsColimit (CokernelCofork.ofπ q hvq)) [Epi e] (hw : w ≫ p = e ≫ v)
    (α : S ≅ D ⨿ C') (β : E' ≅ E) :
    IsColimit (CokernelCofork.ofπ (β.hom ≫ p ≫ q)
      (conj_comp_eq_zero hup hvq hw α β)) := by
  haveI hpe : Epi p := epi_of_isColimit_cofork hp
  haveI hqe : Epi q := epi_of_isColimit_cofork hq
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk => ?_)
  have hk0 : coprod.desc u w ≫ (β.inv ≫ k) = 0 := by
    rw [← cancel_epi α.hom, comp_zero]
    simpa using hk
  have hu0 : u ≫ (β.inv ≫ k) = 0 := by
    have h := coprod.inl ≫= hk0
    rwa [coprod.inl_desc_assoc, comp_zero] at h
  have hw0 : w ≫ (β.inv ≫ k) = 0 := by
    have h := coprod.inr ≫= hk0
    rwa [coprod.inr_desc_assoc, comp_zero] at h
  obtain ⟨l₁, hl₁⟩ := CokernelCofork.IsColimit.desc' hp (β.inv ≫ k) hu0
  rw [CokernelCofork.π_ofπ] at hl₁
  have hvl : v ≫ l₁ = 0 := by
    refine (cancel_epi e).mp ?_
    rw [comp_zero, ← Category.assoc, ← hw, Category.assoc, hl₁, hw0]
  obtain ⟨l₂, hl₂⟩ := CokernelCofork.IsColimit.desc' hq l₁ hvl
  rw [CokernelCofork.π_ofπ] at hl₂
  refine ⟨l₂, ?_⟩
  rw [Category.assoc, Category.assoc, hl₂, hl₁, Iso.hom_inv_id_assoc]

end MiyaokaMori.CokernelComp

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {A B KA KB M N : X.Modules}

theorem whiskerLeft_comp_eq_zero (A : X.Modules) {rB : KB ⟶ B} {πB : B ⟶ N}
    (hB0 : rB ≫ πB = 0) : (A ◁ rB) ≫ (A ◁ πB) = 0 := by
  rw [← MonoidalCategory.whiskerLeft_comp, hB0]
  exact (MonoidalCategory.tensorLeft A).map_zero _ _

theorem comp_whiskerRight_eq_zero (N : X.Modules) {rA : KA ⟶ A} {πA : A ⟶ M}
    (hA0 : rA ≫ πA = 0) : (rA ▷ N) ≫ (πA ▷ N) = 0 := by
  rw [← MonoidalCategory.comp_whiskerRight, hA0]
  exact (MonoidalCategory.tensorRight N).map_zero _ _

/-- `A ⊗ (-)` sends the cokernel presentation `B ↠ N` to a cokernel presentation `A ⊗ B ↠ A ⊗ N`. -/
def tensorLeftCokernel (A : X.Modules) {rB : KB ⟶ B} {πB : B ⟶ N} {hB0 : rB ≫ πB = 0}
    (hB : IsColimit (CokernelCofork.ofπ πB hB0)) :
    IsColimit (CokernelCofork.ofπ (f := A ◁ rB) (A ◁ πB)
      (whiskerLeft_comp_eq_zero A hB0)) :=
  haveI : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft A) :=
    preservesColimitsOfSize_shrink _
  CokernelCofork.mapIsColimit _ hB (MonoidalCategory.tensorLeft A)

/-- `(-) ⊗ N` sends the cokernel presentation `A ↠ M` to a cokernel presentation `A ⊗ N ↠ M ⊗ N`. -/
def tensorRightCokernel (N : X.Modules) {rA : KA ⟶ A} {πA : A ⟶ M} {hA0 : rA ≫ πA = 0}
    (hA : IsColimit (CokernelCofork.ofπ πA hA0)) :
    IsColimit (CokernelCofork.ofπ (f := rA ▷ N) (πA ▷ N)
      (comp_whiskerRight_eq_zero N hA0)) :=
  haveI : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight N) :=
    preservesColimitsOfSize_shrink _
  CokernelCofork.mapIsColimit _ hA (MonoidalCategory.tensorRight N)

/-- **Cokernel presentation of the tensor product** (already conjugated along `α`, `β`, ready to be
rewritten with free sheaves). -/
def tensorCokernelConj {S E' : X.Modules}
    {rA : KA ⟶ A} {πA : A ⟶ M} {hA0 : rA ≫ πA = 0}
    (hA : IsColimit (CokernelCofork.ofπ πA hA0))
    {rB : KB ⟶ B} {πB : B ⟶ N} {hB0 : rB ≫ πB = 0}
    (hB : IsColimit (CokernelCofork.ofπ πB hB0))
    (α : S ≅ (A ⊗ KB) ⨿ (KA ⊗ B)) (β : E' ≅ A ⊗ B) :
    IsColimit (CokernelCofork.ofπ
      (f := α.hom ≫ coprod.desc (A ◁ rB) (rA ▷ B) ≫ β.inv)
      (β.hom ≫ (A ◁ πB) ≫ (πA ▷ N))
      (MiyaokaMori.CokernelComp.conj_comp_eq_zero
        (whiskerLeft_comp_eq_zero A hB0) (comp_whiskerRight_eq_zero N hA0)
        (MonoidalCategory.whisker_exchange rA πB).symm α β)) :=
  haveI : Epi πB := epi_of_isColimit_cofork hB
  haveI : Epi (KA ◁ πB) :=
    (MonoidalCategory.tensorLeft KA).map_epi πB
  MiyaokaMori.CokernelComp.isColimitConj
    (tensorLeftCokernel A hB) (tensorRightCokernel N hA)
    (MonoidalCategory.whisker_exchange rA πB).symm α β

/-- Mathlib's `freeSumIso`, spelled for `X.Modules`. -/
def freeSumIsoX (X : AlgebraicGeometry.Scheme.{u}) (I J : Type u) :
    ((SheafOfModules.free (R := X.ringCatSheaf) I ⨿
        SheafOfModules.free (R := X.ringCatSheaf) J : X.Modules)) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (I ⊕ J) :=
  SheafOfModules.freeSumIso I J

/-- **A global presentation of `M ⊗ N` from global presentations of `M` and `N`** (the algebraic core
of Stacks 01CE). The generators are indexed by `σM × σN`, the relations by `(σM × ιN) ⊕ (ιM × σN)`. -/
def tensorPresentation (P : SheafOfModules.Presentation.{u} M)
    (Q : SheafOfModules.Presentation.{u} N) :
    SheafOfModules.Presentation.{u}
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) M N) :=
  SheafOfModules.presentationOfIsCokernelFree _ _ _
    (tensorCokernelConj P.isColimit Q.isColimit
      ((CategoryTheory.Limits.coprod.mapIso
          (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso
            P.generators.I Q.relations.I)
          (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso
            P.relations.I Q.generators.I)) ≪≫
        freeSumIsoX X _ _).symm
      (AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso
        P.generators.I Q.generators.I).symm)

end AlgebraicGeometry.Scheme.Modules

end
