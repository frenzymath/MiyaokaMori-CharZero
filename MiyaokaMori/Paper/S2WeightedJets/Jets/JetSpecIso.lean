import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetCoordinateAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetSchemeAffineOverBase
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty

/-! # The jet scheme as a relative Spec

`J_k^s ≅ Spec_C S` (the correspondence between relative Spec and affine morphisms; §2 of the paper,
`J_k^s = Spec_C 𝒮`).

Route (Stacks 01SA / 01LY): for an arbitrary affine morphism `π = T.hom : T → X`, let
`S := pushforwardStructureSheaf π` (`= π_*O_T`).
1. The multiplication and unit of the sections ring `S.sectionsRing U` are those of `Γ(T, π⁻¹U)`
   (`sectionsRing_mul`, `sectionsRing_one`): by definition `QCAlgebra.presheafMul S` is
   `adj.homEquiv (μ⁻¹ ≫ (e ⊗ e) ≫ S.mul)`, while `S.mul = (e⁻¹ ⊗ e⁻¹) ≫ μ ≫ L(m) ≫ e` (`m` the open-by-open
   multiplication); after cancellation this is `m` (`qcPresheafMul_eq`).
2. Hence the identity `𝟙 : S.carrier ⟶ π_*O_T` is a map of `O_X`-algebras (`id_isAlgebraMapToPushforward`), and
   the universal property `relativeSpec.ofAlgebraMap` gives a canonical `X`-morphism `can : T → Spec_X S`.
3. `can` is an isomorphism (`isIso_ofAlgebraMap_id_left`): `ι_ofAlgebraMap_left` says that on `π⁻¹W` (`W` an
   affine open) `can = toSpecΓ ≫ Spec(identity) ≫ chart W`; the first two are isomorphisms and `chart W` is an
   open immersion, so `can` is an open immersion piecewise; `can` is injective on points (two points with the same
   image lie in a common `π⁻¹W`, where the piece is injective), so `IsOpenImmersion.of_openCover_source` makes `can`
   an open immersion; the charts jointly cover (`AffineAlgebra.exists_chart_mem`), so `can` is surjective; an
   open immersion that is surjective is an isomorphism.
4. `Over.forget` reflects isomorphisms, giving an isomorphism in `Over C`; the coordinate algebra of `J_k^s` is
   by definition `π_*O_J`, whence `jetSchemeIsoRelativeSpec`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf-level multiplication `QCAlgebra.presheafMul` of `pushforwardStructureSheaf f`
    is the pointwise multiplication `pushforwardStructureSheaf.presheafMul f` (the multiplication of `Γ(T, f⁻¹U)`):
    the sheafification comparison isomorphisms `μ` and the counit isomorphisms `e` cancel. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.qcPresheafMul_eq
    {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) [AlgebraicGeometry.IsAffineHom f] :
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf f).presheafMul =
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul f := by
  unfold AlgebraicGeometry.Scheme.QCAlgebra.presheafMul
  dsimp only
  rw [Adjunction.homEquiv_apply_eq, Adjunction.homEquiv_counit]
  rw [show (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf f).mul =
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f from rfl]
  unfold AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [show ((asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf f).carrier) =
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f from rfl]
  rw [Iso.hom_inv_id, MonoidalCategory.id_tensorHom_id, Category.id_comp]
  erw [Iso.inv_hom_id_assoc]
  rfl

/-- Multiplication in the sections ring of `f_*O_T` is the multiplication of `Γ(T, f⁻¹U)`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sectionsRing_mul
    {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) [AlgebraicGeometry.IsAffineHom f]
    (U : X.Opens)
    (a b : (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf f).sectionsRing U) :
    a * b = ((show Γ(T, f ⁻¹ᵁ U) from a) * (show Γ(T, f ⁻¹ᵁ U) from b) : Γ(T, f ⁻¹ᵁ U)) := by
  show (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf f).sectionsMul U a b = _
  unfold AlgebraicGeometry.Scheme.QCAlgebra.sectionsMul
  rw [AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.qcPresheafMul_eq]
  rfl

/-- The unit of the sections ring of `f_*O_T` is `1 ∈ Γ(T, f⁻¹U)`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sectionsRing_one
    {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) [AlgebraicGeometry.IsAffineHom f]
    (U : X.Opens) :
    (1 : (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf f).sectionsRing U) =
      (show Γ(T, f ⁻¹ᵁ U) from 1) := by
  exact map_one (f.c.app (Opposite.op U)).hom

set_option backward.isDefEq.respectTransparency false in
/-- The identity `f_*O_T → f_*O_T` is a map of `O_X`-algebras. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.id_isAlgebraMapToPushforward
    {X : AlgebraicGeometry.Scheme.{u}} (T : CategoryTheory.Over X)
    [AlgebraicGeometry.IsAffineHom T.hom] :
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).IsAlgebraMapToPushforward
      T.hom (CategoryTheory.CategoryStruct.id _) := by
  refine ⟨fun U a b => ?_, fun U => ?_⟩
  · exact ((AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).sectionsMul_eq_mul_tensorSections
      U a b).symm.trans
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sectionsRing_mul T.hom U a b)
  · exact AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sectionsRing_one T.hom U


set_option backward.isDefEq.respectTransparency false in
/-- Stacks 01SA: for an affine morphism `T.hom : T → X`, the canonical `X`-morphism
    `T → Spec_X ((T.hom)_* O_T)` (the universal property applied to the identity algebra map)
    is an isomorphism of schemes. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.isIso_ofAlgebraMap_id_left
    {X : AlgebraicGeometry.Scheme.{u}} (T : CategoryTheory.Over X)
    [AlgebraicGeometry.IsAffineHom T.hom] :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom) T
      (CategoryTheory.CategoryStruct.id _)
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.id_isAlgebraMapToPushforward
        T)).left := by
  set A := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom with hA
  set hφ := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.id_isAlgebraMapToPushforward T
    with hhφ
  set can := (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap A T
    (CategoryTheory.CategoryStruct.id _) hφ).left with hcan
  have hloc : ∀ W : X.AffineZariskiSite, (T.hom ⁻¹ᵁ W.toOpens).ι ≫ can =
      (T.hom ⁻¹ᵁ W.toOpens).toSpecΓ ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (A.algebraMapSections T.hom (CategoryTheory.CategoryStruct.id _) hφ W.toOpens)) ≫
        A.toAffineAlgebra.chart W :=
    fun W => AlgebraicGeometry.Scheme.relativeSpec.ι_ofAlgebraMap_left A T _ hφ W
  have hiso1 : ∀ W : X.AffineZariskiSite, IsIso (T.hom ⁻¹ᵁ W.toOpens).toSpecΓ := fun W => by
    rw [← (W.2.preimage T.hom).isoSpec_hom]; infer_instance
  have hiso2 : ∀ W : X.AffineZariskiSite, IsIso (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (A.algebraMapSections T.hom (CategoryTheory.CategoryStruct.id _) hφ W.toOpens))) := fun W => by
    have : IsIso (CommRingCat.ofHom
        (A.algebraMapSections T.hom (CategoryTheory.CategoryStruct.id _) hφ W.toOpens)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b h => h, fun b => ⟨b, rfl⟩⟩
    infer_instance
  have hoi : ∀ W : X.AffineZariskiSite,
      AlgebraicGeometry.IsOpenImmersion ((T.hom ⁻¹ᵁ W.toOpens).ι ≫ can) := fun W => by
    rw [hloc W]
    haveI := hiso1 W
    haveI := hiso2 W
    infer_instance
  have hw : can ≫ (AlgebraicGeometry.Scheme.relativeSpec A).hom = T.hom := CategoryTheory.Over.w _
  have hinj : Function.Injective can := by
    intro x y hxy
    have hT : T.hom x = T.hom y := by
      rw [← hw, AlgebraicGeometry.Scheme.Hom.comp_apply, AlgebraicGeometry.Scheme.Hom.comp_apply, hxy]
    obtain ⟨W, hWaff, hxW, -⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := T.hom x) (U := ⊤) trivial
    have hyW : T.hom y ∈ W := hT ▸ hxW
    let W' : X.AffineZariskiSite := ⟨W, hWaff⟩
    haveI := hoi W'
    have h2 : ((T.hom ⁻¹ᵁ W'.toOpens).ι ≫ can) ⟨x, hxW⟩ =
        ((T.hom ⁻¹ᵁ W'.toOpens).ι ≫ can) ⟨y, hyW⟩ := by
      rw [AlgebraicGeometry.Scheme.Hom.comp_apply, AlgebraicGeometry.Scheme.Hom.comp_apply]
      exact hxy
    exact congrArg Subtype.val (((T.hom ⁻¹ᵁ W'.toOpens).ι ≫ can).isOpenEmbedding.injective h2)
  have hsurj : Function.Surjective can := by
    intro z
    obtain ⟨W, y, hy⟩ := A.toAffineAlgebra.exists_chart_mem z
    haveI := hiso1 W
    haveI := hiso2 W
    have hchart : A.toAffineAlgebra.chart W =
        CategoryTheory.inv ((T.hom ⁻¹ᵁ W.toOpens).toSpecΓ ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom
            (A.algebraMapSections T.hom (CategoryTheory.CategoryStruct.id _) hφ W.toOpens))) ≫
          ((T.hom ⁻¹ᵁ W.toOpens).ι ≫ can) := by
      rw [CategoryTheory.IsIso.eq_inv_comp, hloc W, CategoryTheory.Category.assoc]
    refine ⟨(T.hom ⁻¹ᵁ W.toOpens).ι (CategoryTheory.inv ((T.hom ⁻¹ᵁ W.toOpens).toSpecΓ ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (A.algebraMapSections T.hom (CategoryTheory.CategoryStruct.id _) hφ W.toOpens))) y), ?_⟩
    rw [← hy, hchart, AlgebraicGeometry.Scheme.Hom.comp_apply,
      AlgebraicGeometry.Scheme.Hom.comp_apply]
    rfl
  have hoi' : AlgebraicGeometry.IsOpenImmersion can :=
    AlgebraicGeometry.IsOpenImmersion.of_openCover_source can
      (AlgebraicGeometry.Scheme.preimageAffineCover T.hom) hinj (fun W => hoi W)
  rw [AlgebraicGeometry.isIso_iff_isOpenImmersion_and_epi_base]
  exact ⟨hoi', (TopCat.epi_iff_surjective _).mpr hsurj⟩

/-- `J_k^s ≅ Spec_C S` in `Over C` (§2 of the paper): the coordinate algebra
    `jetCoordinateAlgebra` is by definition `π_*O_{J}` for the affine structure morphism π, so this is
    the general statement `isIso_ofAlgebraMap_id_left` (Stacks 01SA) for `T := J_k^s`. -/
theorem jetSchemeIsoRelativeSpec {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
    [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    Nonempty (relativeJetScheme (k := k) Z s hs r ≅
      AlgebraicGeometry.Scheme.relativeSpec (jetCoordinateAlgebra (k := k) Z s hs r)) := by
  haveI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.isIso_ofAlgebraMap_id_left
    (relativeJetScheme (k := k) Z s hs r)
  haveI : CategoryTheory.IsIso ((CategoryTheory.Over.forget C).map
      (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf
          (relativeJetScheme (k := k) Z s hs r).hom)
        (relativeJetScheme (k := k) Z s hs r) (CategoryTheory.CategoryStruct.id _)
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.id_isAlgebraMapToPushforward
          (relativeJetScheme (k := k) Z s hs r)))) := this
  have hI : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf
        (relativeJetScheme (k := k) Z s hs r).hom)
      (relativeJetScheme (k := k) Z s hs r) (CategoryTheory.CategoryStruct.id _)
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.id_isAlgebraMapToPushforward
        (relativeJetScheme (k := k) Z s hs r))) :=
    CategoryTheory.isIso_of_reflects_iso _ (CategoryTheory.Over.forget C)
  exact ⟨@CategoryTheory.asIso _ _ _ _ _ hI⟩


end
