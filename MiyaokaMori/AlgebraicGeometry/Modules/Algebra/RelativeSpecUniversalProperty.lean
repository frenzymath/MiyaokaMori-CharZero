import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.TrivialLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpec
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra

/-! # The universal property of the relative Spec

The universal property of the relative Spec: `Hom_X(T, Spec_X A) ≃ Hom_{O_X-alg}(A, g_* O_T)`
(Stacks 01LQ).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `φ : A → g_* O_T` is a map of `O_X`-algebras: on every open `U`, the section map `A(U) → Γ(T, g⁻¹U)` of `φ`
is compatible with the multiplication `A.mul` and unit `A.one` of `A` and the multiplication and unit of
`O_T` (no quasi-coherence of `g_* O_T` is required). -/
def AlgebraicGeometry.Scheme.QCAlgebra.IsAlgebraMapToPushforward {X T : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (g : T ⟶ X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf)) : Prop :=
  -- multiplication: `φ(a·b) = φ(a)φ(b)`, where `a·b` is `A.mul` on the section pairing `tensorSections`;
  -- the right side is the product in `Γ(T, g⁻¹U)`
  (∀ (U : X.Opens) (a b : A.carrier.val.obj (Opposite.op U)),
      (show Γ(T, g ⁻¹ᵁ U) from φ.app U (A.mul.app U
          (AlgebraicGeometry.Scheme.Modules.tensorSections A.carrier A.carrier U a b))) =
        (show Γ(T, g ⁻¹ᵁ U) from φ.app U a) * (show Γ(T, g ⁻¹ᵁ U) from φ.app U b)) ∧
  -- unit: `φ(1) = 1`, where `1` is the unit section of `𝟙_ = O_X` on `U`
  (∀ U : X.Opens,
      (show Γ(T, g ⁻¹ᵁ U) from φ.app U (A.one.app U (show Γ(X, U) from 1))) = 1)

/-- The ring homomorphism `A(U) → Γ(T, g⁻¹U)` on sections over an open `U` of an algebra map `φ` (the ring
structure of `A(U)` is `QcAlgebraSectionsRing.lean`). Preservation of multiplication and unit comes from
`IsAlgebraMapToPushforward`, via `sectionsMul = A.mul ∘ tensorSections`. -/
noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.algebraMapSections {X T : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (g : T ⟶ X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward g φ) (U : X.Opens) :
    A.sectionsRing U →+* Γ(T, g ⁻¹ᵁ U) where
  toFun a := (show Γ(T, g ⁻¹ᵁ U) from φ.app U a)
  map_zero' := map_zero (φ.app U).hom
  map_add' := map_add (φ.app U).hom
  map_one' := hφ.2 U
  map_mul' := fun a b => hφ.1 U a b

/-- `φ` is compatible with the structure map: `φ(r·1_A) = g^♯(r)`. From the `O_X`-linearity of `A.one` and `φ`
(`Modules.Hom.app_smul`) and `φ(1) = 1`; the scalar action of `r` on `g_*O_T` is multiplication by `g^♯(r)`. -/

theorem AlgebraicGeometry.Scheme.QCAlgebra.algebraMapSections_comp_sectionsUnit
    {X T : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (g : T ⟶ X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward g φ) (U : X.Opens) (r : Γ(X, U)) :
    A.algebraMapSections g φ hφ U (A.sectionsUnit U r) = (g.app U).hom r := by
  have hone : φ.app U (A.one.app U (1 : Γ(X, U))) = (1 : Γ(T, g ⁻¹ᵁ U)) := hφ.2 U
  have hunit : (r • (A.one.app U (1 : Γ(X, U)))) = A.one.app U r :=
    (AlgebraicGeometry.Scheme.Modules.Hom.app_smul A.one r _).symm.trans
      (congrArg (fun x : Γ(X, U) => A.one.app U x) (mul_one r))
  show ((φ.app U (A.one.app U r)) : Γ(T, g ⁻¹ᵁ U)) = _
  rw [← hunit, AlgebraicGeometry.Scheme.Modules.Hom.app_smul, hone]
  exact mul_one ((g.app U).hom r)

/-- The `CommRingCat` form of the previous lemma: the structure map `A.toAffineAlgebra.unit` followed by the
section ring homomorphism of `φ` is the sheaf map of `g`. -/

theorem AlgebraicGeometry.Scheme.QCAlgebra.affineUnit_comp_algebraMapSections
    {X T : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (g : T ⟶ X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward g φ) (W : X.AffineZariskiSite) :
    A.toAffineAlgebra.unit.app (Opposite.op W) ≫
        CommRingCat.ofHom (A.algebraMapSections g φ hφ W.toOpens) = g.app W.toOpens := by
  ext r
  exact A.algebraMapSections_comp_sectionsUnit g φ hφ W.toOpens r

/- Each piece `g⁻¹U → Spec A(U) → Spec_X A` lies over `X`: the chart equation `AffineAlgebra.chart_hom` plus the
previous identity of sheaves of rings, finished with `Scheme.Opens.toSpecΓ_naturality` and
`morphismRestrict_ι`. -/

set_option backward.isDefEq.respectTransparency false in
theorem AlgebraicGeometry.Scheme.QCAlgebra.chart_comp_relativeSpec_hom
    {X T : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (g : T ⟶ X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward g φ) (W : X.AffineZariskiSite) :
    ((g ⁻¹ᵁ W.toOpens).toSpecΓ ≫ AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (A.algebraMapSections g φ hφ W.toOpens)) ≫
      A.toAffineAlgebra.chart W) ≫ A.toAffineAlgebra.relativeSpec.hom
      = (g ⁻¹ᵁ W.toOpens).ι ≫ g := by
  rw [CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
    AlgebraicGeometry.Scheme.AffineAlgebra.chart_hom,
    AlgebraicGeometry.Scheme.AffineAlgebra.chartToOpen, CategoryTheory.Category.assoc,
    ← AlgebraicGeometry.Spec.map_comp_assoc,
    A.affineUnit_comp_algebraMapSections g φ hφ W,
    AlgebraicGeometry.Scheme.Opens.toSpecΓ_naturality_assoc,
    ← AlgebraicGeometry.IsAffineOpen.isoSpec_hom W.2, CategoryTheory.Iso.hom_inv_id_assoc,
    AlgebraicGeometry.morphismRestrict_ι]

/-- The section ring homomorphisms of `φ` are compatible with restriction (naturality of `φ` as a morphism of
sheaves of modules). -/

theorem AlgebraicGeometry.Scheme.QCAlgebra.algebraMapSections_naturality
    {X T : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (g : T ⟶ X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward g φ) {W U : X.Opens} (h : W ≤ U) :
    CommRingCat.ofHom (A.algebraMapSections g φ hφ U) ≫
        T.presheaf.map (CategoryTheory.homOfLE (g.preimage_mono h)).op =
      CommRingCat.ofHom (A.sectionsRestrict h) ≫
        CommRingCat.ofHom (A.algebraMapSections g φ hφ W) := by
  ext a
  exact (_root_.PresheafOfModules.naturality_apply φ.val (CategoryTheory.homOfLE h).op a).symm

/- The piece morphisms are compatible with restriction: for `W` a principal open of `U`, `g⁻¹W ↪ g⁻¹U` followed
by the morphism of the `U`-piece is the morphism of the `W`-piece. -/

set_option backward.isDefEq.respectTransparency false in
theorem AlgebraicGeometry.Scheme.QCAlgebra.chartMap_restrict
    {X T : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (g : T ⟶ X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward g φ) {W U : X.AffineZariskiSite} (h : W ≤ U) :
    T.homOfLE (g.preimage_mono (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono h)) ≫
        ((g ⁻¹ᵁ U.toOpens).toSpecΓ ≫ AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (A.algebraMapSections g φ hφ U.toOpens)) ≫
          A.toAffineAlgebra.chart U) =
      (g ⁻¹ᵁ W.toOpens).toSpecΓ ≫ AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (A.algebraMapSections g φ hφ W.toOpens)) ≫
        A.toAffineAlgebra.chart W := by
  rw [← AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc
      (g ⁻¹ᵁ W.toOpens) (g ⁻¹ᵁ U.toOpens)
      (g.preimage_mono (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono h)),
    ← AlgebraicGeometry.Spec.map_comp_assoc,
    A.algebraMapSections_naturality g φ hφ
      (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono h),
    AlgebraicGeometry.Spec.map_comp_assoc]
  have hc : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (A.sectionsRestrict
        (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono h))) ≫
        A.toAffineAlgebra.chart U = A.toAffineAlgebra.chart W :=
    A.toAffineAlgebra.map_chart h
  rw [hc]

/-- `T` is covered by the `g⁻¹U` (`U` ranging over the affine opens of `X`); the index category is Mathlib's small
affine Zariski site (objects: affine opens, arrows: inclusions of principal opens), which gives local
directedness (overlaps are covered by affine opens that are principal opens of both sides). -/

theorem AlgebraicGeometry.Scheme.isOpenCover_preimage_affineZariski
    {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) :
    TopologicalSpace.IsOpenCover (fun U : X.AffineZariskiSite => g ⁻¹ᵁ U.toOpens) := by
  rw [TopologicalSpace.IsOpenCover, eq_top_iff]
  intro t _
  obtain ⟨W, hW, htW, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := g.base t) (U := ⊤) trivial
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW⟩, htW⟩

noncomputable def AlgebraicGeometry.Scheme.preimageAffineCover
    {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) : T.OpenCover :=
  T.openCoverOfIsOpenCover (fun U : X.AffineZariskiSite => g ⁻¹ᵁ U.toOpens)
    (AlgebraicGeometry.Scheme.isOpenCover_preimage_affineZariski g)

instance AlgebraicGeometry.Scheme.preimageAffineCover_category
    {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) :
    CategoryTheory.Category (AlgebraicGeometry.Scheme.preimageAffineCover g).I₀ :=
  inferInstanceAs (CategoryTheory.Category X.AffineZariskiSite)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance AlgebraicGeometry.Scheme.preimageAffineCover_locallyDirected
    {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) :
    (AlgebraicGeometry.Scheme.preimageAffineCover g).LocallyDirected where
  trans {i j} hij :=
    T.homOfLE (g.preimage_mono
      (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono (CategoryTheory.leOfHom hij)))
  trans_id i := T.homOfLE_rfl _
  trans_comp hij hjk := (T.homOfLE_homOfLE _ _).symm
  w hij := T.homOfLE_ι _
  property_trans {i j} hij :=
    inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (T.homOfLE
      (g.preimage_mono (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono
        (CategoryTheory.leOfHom hij)))))
  directed {i j} x := by
    let a := (CategoryTheory.Limits.pullback.fst
      ((g ⁻¹ᵁ i.toOpens).ι) ((g ⁻¹ᵁ j.toOpens).ι) ≫ (g ⁻¹ᵁ i.toOpens).ι) x
    have hai : a ∈ g ⁻¹ᵁ i.toOpens :=
      (CategoryTheory.Limits.pullback.fst ((g ⁻¹ᵁ i.toOpens).ι) ((g ⁻¹ᵁ j.toOpens).ι) x).2
    have haj : a ∈ g ⁻¹ᵁ j.toOpens := by
      show _ ∈ _
      unfold a
      rw [CategoryTheory.Limits.pullback.condition]
      exact (CategoryTheory.Limits.pullback.snd
        ((g ⁻¹ᵁ i.toOpens).ι) ((g ⁻¹ᵁ j.toOpens).ι) x).2
    obtain ⟨f₁, f₂, e, hxf⟩ :=
      AlgebraicGeometry.exists_basicOpen_le_affine_inter i.2 j.2 (g.base a) ⟨hai, haj⟩
    refine ⟨i.basicOpen f₁,
      (CategoryTheory.homOfLE (i.basicOpen_le f₁) :
        (i.basicOpen f₁ : X.AffineZariskiSite) ⟶ i),
      ((CategoryTheory.eqToHom (Subtype.ext (by exact e)) ≫
        CategoryTheory.homOfLE (j.basicOpen_le f₂) :
          (i.basicOpen f₁ : X.AffineZariskiSite) ⟶ j)), ⟨a, hxf⟩, ?_⟩
    apply (CategoryTheory.Limits.pullback.fst
      ((g ⁻¹ᵁ i.toOpens).ι) ((g ⁻¹ᵁ j.toOpens).ι) ≫ (g ⁻¹ᵁ i.toOpens).ι).isOpenEmbedding.injective
    show (CategoryTheory.Limits.pullback.lift _ _ _ ≫
      CategoryTheory.Limits.pullback.fst _ _ ≫ (g ⁻¹ᵁ i.toOpens).ι) _ =
      (CategoryTheory.Limits.pullback.fst _ _ ≫ (g ⁻¹ᵁ i.toOpens).ι) x
    rw [CategoryTheory.Limits.pullback.lift_fst_assoc, AlgebraicGeometry.Scheme.homOfLE_ι]
    rfl

/-- One direction of Stacks 01LQ: an algebra map `φ : A → g_*O_T` ↦ an `X`-morphism `T → Spec_X A`.
`T` is covered by the `g⁻¹U` (`U` over the objects of the small affine Zariski site of `X`); on `g⁻¹U` take
`g⁻¹U → Spec Γ(T, g⁻¹U) → Spec A(U) ↪ Spec_X A` (Mathlib `Opens.toSpecΓ`, the section ring homomorphism of `φ`,
the chart `AffineAlgebra.chart`), and glue with Mathlib's `OpenCover.glueMorphismsOverOfLocallyDirected`: the
cover is locally directed (`preimageAffineCover_locallyDirected`), so compatibility on overlaps reduces to
compatibility with restriction (`chartMap_restrict`); "over `X`" is `chart_comp_relativeSpec_hom`. -/

noncomputable def AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (T : CategoryTheory.Over X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
      (SheafOfModules.unit T.left.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward T.hom φ) :
    T ⟶ AlgebraicGeometry.Scheme.relativeSpec A :=
  AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOverOfLocallyDirected
    (AlgebraicGeometry.Scheme.preimageAffineCover T.hom)
    (fun U => (T.hom ⁻¹ᵁ U.toOpens).toSpecΓ ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (A.algebraMapSections T.hom φ hφ U.toOpens)) ≫
      A.toAffineAlgebra.chart U)
    (fun {_ _} hij => A.chartMap_restrict T.hom φ hφ (CategoryTheory.leOfHom hij))
    (fun U => A.chart_comp_relativeSpec_hom T.hom φ hφ U)

/-- On an affine open `U`, the map `A(U) → Γ(Spec_X A, π⁻¹U)`: `A(U) ≅ Γ(Spec A(U), ⊤)` (`ΓSpecIso`) transported to
`π⁻¹U` by `affineIso`. -/

noncomputable def AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.affineOpens) :
    CommRingCat.of (A.sectionsRing U.1) ⟶
      Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1) :=
  (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (A.sectionsRing U.1))).inv ≫
    (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).hom.appTop ≫
    ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).topIso.hom

/-- Compatibility of the charts for an arbitrary inclusion of affine opens `V ≤ U` (not necessarily a principal
open). `AffineAlgebra.map_chart` holds only for arrows of the small affine Zariski site (inclusions of
principal opens `D(f) ⊆ U`); here the `D(f)` that are principal opens of both `U` and `V` cover `Spec A(V)`, and
the claim is reduced piece by piece. -/

theorem AlgebraicGeometry.Scheme.QCAlgebra.specMap_chart
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) {U V : X.AffineZariskiSite}
    (hVU : V.toOpens ≤ U.toOpens) :
    AlgebraicGeometry.Spec.map (A.ringPresheaf.map (CategoryTheory.homOfLE hVU).op) ≫
        A.toAffineAlgebra.chart U = A.toAffineAlgebra.chart V := by
  classical
  -- index: the sections `f` on `U` with `D(f) ⊆ V`
  set J := {f : Γ(X, U.toOpens) // X.basicOpen f ≤ V.toOpens} with hJ
  set g : J → Γ(X, V.toOpens) :=
    fun f => (X.presheaf.map (CategoryTheory.homOfLE hVU).op) f.1 with hg
  have hbo : ∀ f : J, X.basicOpen (g f) = X.basicOpen f.1 := by
    intro f
    show X.basicOpen ((X.presheaf.map (CategoryTheory.homOfLE hVU).op) f.1) = _
    rw [AlgebraicGeometry.Scheme.basicOpen_res]
    exact inf_eq_right.mpr f.2
  set W : J → X.AffineZariskiSite := fun f => V.basicOpen (g f) with hW
  have hWV : ∀ f : J, W f ≤ V := fun f => V.basicOpen_le (g f)
  have hWU : ∀ f : J, W f ≤ U := fun f => ⟨f.1, (hbo f).symm⟩
  have leWV : ∀ f : J, (W f).toOpens ≤ V.toOpens :=
    fun f => AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono (hWV f)
  have leWU : ∀ f : J, (W f).toOpens ≤ U.toOpens :=
    fun f => AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono (hWU f)
  -- these `D(f)` cover `Spec A(V)`
  have hcov : ∀ x : AlgebraicGeometry.Spec (A.toAffineAlgebra.sections V), ∃ (f : J)
      (y : AlgebraicGeometry.Spec (A.toAffineAlgebra.sections (W f))),
      (A.toAffineAlgebra.gluingData.functor.map (CategoryTheory.homOfLE (hWV f))) y = x := by
    intro x
    set p : X :=
      V.2.fromSpec.base ((AlgebraicGeometry.Spec.map (A.affineUnit.app (Opposite.op V))).base x)
      with hp
    have hpV : p ∈ V.toOpens := by
      have hmem : p ∈ Set.range V.2.fromSpec.base := ⟨_, rfl⟩
      rw [V.2.range_fromSpec] at hmem
      exact hmem
    obtain ⟨f, hf1, hf2⟩ := U.2.exists_basicOpen_le (V := V.toOpens) ⟨p, hpV⟩ (hVU hpV)
    refine ⟨⟨f, hf1⟩, ?_⟩
    have hrange := AlgebraicGeometry.Scheme.AffineZariskiSite.opensRange_relativeGluingData_map
      _ A.affineUnit A.unit_coequifibered (U := V) (g ⟨f, hf1⟩)
    have hx : x ∈ ((AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData
        A.unit_coequifibered).functor.map
        (CategoryTheory.homOfLE (hWV ⟨f, hf1⟩))).opensRange := by
      rw [hrange]
      have hpb : p ∈ X.basicOpen (g ⟨f, hf1⟩) := by rw [hbo ⟨f, hf1⟩]; exact hf2
      have h2 : ((AlgebraicGeometry.Spec.map (A.affineUnit.app (Opposite.op V))).base x) ∈
          PrimeSpectrum.basicOpen (g ⟨f, hf1⟩) := by
        rw [← V.2.fromSpec_preimage_basicOpen (g ⟨f, hf1⟩)]
        exact hpb
      exact h2
    exact hx
  let 𝒰 : AlgebraicGeometry.Scheme.OpenCover
      (AlgebraicGeometry.Spec (A.toAffineAlgebra.sections V)) :=
    AlgebraicGeometry.Scheme.Cover.mkOfCovers J
      (fun f => AlgebraicGeometry.Spec (A.toAffineAlgebra.sections (W f)))
      (fun f => A.toAffineAlgebra.gluingData.functor.map (CategoryTheory.homOfLE (hWV f))) hcov
      (fun f => A.toAffineAlgebra.gluingData.instIsOpenImmersionMapI₀Functor
        (CategoryTheory.homOfLE (hWV f)))
  -- piecewise: both sides reduce to `chart (W j)`
  have main : ∀ j : J,
      AlgebraicGeometry.Spec.map (A.ringPresheaf.map (CategoryTheory.homOfLE (leWV j)).op) ≫
          (AlgebraicGeometry.Spec.map (A.ringPresheaf.map (CategoryTheory.homOfLE hVU).op) ≫
            A.toAffineAlgebra.chart U) =
        AlgebraicGeometry.Spec.map (A.ringPresheaf.map (CategoryTheory.homOfLE (leWV j)).op) ≫
          A.toAffineAlgebra.chart V := by
    intro j
    have hcomp : A.ringPresheaf.map (CategoryTheory.homOfLE hVU).op ≫
        A.ringPresheaf.map (CategoryTheory.homOfLE (leWV j)).op =
        A.ringPresheaf.map (CategoryTheory.homOfLE (leWU j)).op := by
      rw [← A.ringPresheaf.map_comp]
      rfl
    have step1 :
        AlgebraicGeometry.Spec.map (A.ringPresheaf.map (CategoryTheory.homOfLE (leWV j)).op) ≫
          AlgebraicGeometry.Spec.map (A.ringPresheaf.map (CategoryTheory.homOfLE hVU).op) =
        AlgebraicGeometry.Spec.map (A.ringPresheaf.map (CategoryTheory.homOfLE (leWU j)).op) := by
      rw [← AlgebraicGeometry.Spec.map_comp, hcomp]
    have mc1 : AlgebraicGeometry.Spec.map (A.ringPresheaf.map (CategoryTheory.homOfLE (leWV j)).op) ≫
        A.toAffineAlgebra.chart V = A.toAffineAlgebra.chart (W j) :=
      AlgebraicGeometry.Scheme.AffineAlgebra.map_chart A.toAffineAlgebra (hWV j)
    have mc2 : AlgebraicGeometry.Spec.map (A.ringPresheaf.map (CategoryTheory.homOfLE (leWU j)).op) ≫
        A.toAffineAlgebra.chart U = A.toAffineAlgebra.chart (W j) :=
      AlgebraicGeometry.Scheme.AffineAlgebra.map_chart A.toAffineAlgebra (hWU j)
    exact ((CategoryTheory.Category.assoc _ _ _).symm.trans
      (congrArg (fun m => m ≫ A.toAffineAlgebra.chart U) step1)).trans (mc2.trans mc1.symm)
  exact AlgebraicGeometry.Scheme.Cover.hom_ext 𝒰 _ _ main

/-- The morphism of sheaves of rings `A → π_* O_{Spec_X A}`: `sectionsToFunctions` on the affine opens (a basis),
extended by Mathlib's `TopCat.Sheaf.restrictHomEquivHom` (the target is a sheaf, so a morphism on a basis
extends uniquely to all opens); naturality on the basis is proved below. -/

noncomputable def AlgebraicGeometry.Scheme.relativeSpec.structureRingMap {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) :
    A.ringPresheaf ⟶
      ((TopCat.Sheaf.pushforward CommRingCat.{u} (AlgebraicGeometry.Scheme.relativeSpec A).hom.base).obj
        (AlgebraicGeometry.Scheme.relativeSpec A).left.sheaf).obj :=
  TopCat.Sheaf.restrictHomEquivHom (B := fun U : X.affineOpens => U.1) A.ringPresheaf
    ((TopCat.Sheaf.pushforward CommRingCat.{u} (AlgebraicGeometry.Scheme.relativeSpec A).hom.base).obj
      (AlgebraicGeometry.Scheme.relativeSpec A).left.sheaf)
    (by rw [Subtype.range_coe]; exact X.isBasis_affineOpens)
    { app := fun U => AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions A U.unop
      naturality := by
        intro Uop Vop f
        have h : (Opposite.unop Vop : X.affineOpens).1 ≤ (Opposite.unop Uop : X.affineOpens).1 :=
          CategoryTheory.leOfHom
            ((CategoryTheory.inducedFunctor (fun U : X.affineOpens => U.1)).map f.unop)
        have hpre : (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ (Opposite.unop Vop).1 ≤
            (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ (Opposite.unop Uop).1 :=
          fun x hx => h hx
        set ρ : CommRingCat.of (A.sectionsRing (Opposite.unop Uop).1) ⟶
            CommRingCat.of (A.sectionsRing (Opposite.unop Vop).1) :=
          A.ringPresheaf.map (CategoryTheory.homOfLE h).op with hρ
        have hchart : AlgebraicGeometry.Spec.map ρ ≫
            A.toAffineAlgebra.chart ⟨(Opposite.unop Uop).1, (Opposite.unop Uop).2⟩ =
            A.toAffineAlgebra.chart ⟨(Opposite.unop Vop).1, (Opposite.unop Vop).2⟩ :=
          A.specMap_chart (U := ⟨(Opposite.unop Uop).1, (Opposite.unop Uop).2⟩)
            (V := ⟨(Opposite.unop Vop).1, (Opposite.unop Vop).2⟩) h
        have hj : (AlgebraicGeometry.Scheme.relativeSpec.affineIso A (Opposite.unop Vop)).inv ≫
            (AlgebraicGeometry.Scheme.relativeSpec A).left.homOfLE hpre =
            AlgebraicGeometry.Spec.map ρ ≫
              (AlgebraicGeometry.Scheme.relativeSpec.affineIso A (Opposite.unop Uop)).inv := by
          rw [← CategoryTheory.cancel_mono ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ
              (Opposite.unop Uop).1).ι, CategoryTheory.Category.assoc,
            CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.homOfLE_ι,
            AlgebraicGeometry.Scheme.relativeSpec.affineIso_inv_ι,
            AlgebraicGeometry.Scheme.relativeSpec.affineIso_inv_ι]
          exact hchart.symm
        rw [CategoryTheory.Iso.inv_comp_eq] at hj
        have hj' : (AlgebraicGeometry.Scheme.relativeSpec A).left.homOfLE hpre ≫
            (AlgebraicGeometry.Scheme.relativeSpec.affineIso A (Opposite.unop Uop)).hom =
            (AlgebraicGeometry.Scheme.relativeSpec.affineIso A (Opposite.unop Vop)).hom ≫
              AlgebraicGeometry.Spec.map ρ := by
          rw [hj, CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
            CategoryTheory.Iso.inv_hom_id, CategoryTheory.Category.comp_id]
        have happ := congrArg AlgebraicGeometry.Scheme.Hom.appTop hj'
        rw [AlgebraicGeometry.Scheme.Hom.comp_appTop,
          AlgebraicGeometry.Scheme.Hom.comp_appTop] at happ
        have htop : ((AlgebraicGeometry.Scheme.relativeSpec A).left.homOfLE hpre).appTop ≫
            ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ
              (Opposite.unop Vop).1).topIso.hom =
            ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ
                (Opposite.unop Uop).1).topIso.hom ≫
              (AlgebraicGeometry.Scheme.relativeSpec A).left.presheaf.map
                (CategoryTheory.homOfLE hpre).op := by
          simp only [AlgebraicGeometry.Scheme.homOfLE_appTop,
            AlgebraicGeometry.Scheme.Opens.topIso_hom]
          set_option backward.isDefEq.respectTransparency false in
          rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
          congr 1
        have happ2 : (AlgebraicGeometry.Spec.map ρ).appTop ≫
            (AlgebraicGeometry.Scheme.relativeSpec.affineIso A (Opposite.unop Vop)).hom.appTop ≫
              ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ
                (Opposite.unop Vop).1).topIso.hom =
            (AlgebraicGeometry.Scheme.relativeSpec.affineIso A (Opposite.unop Uop)).hom.appTop ≫
              ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ
                  (Opposite.unop Uop).1).topIso.hom ≫
                (AlgebraicGeometry.Scheme.relativeSpec A).left.presheaf.map
                  (CategoryTheory.homOfLE hpre).op := by
          rw [← CategoryTheory.Category.assoc, ← happ, CategoryTheory.Category.assoc, htop]
        show ρ ≫
            AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions A (Opposite.unop Vop) =
          AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions A (Opposite.unop Uop) ≫
            (AlgebraicGeometry.Scheme.relativeSpec A).left.presheaf.map
              (CategoryTheory.homOfLE hpre).op
        show ρ ≫
            ((AlgebraicGeometry.Scheme.ΓSpecIso
                (CommRingCat.of (A.sectionsRing (Opposite.unop Vop).1))).inv ≫
              (AlgebraicGeometry.Scheme.relativeSpec.affineIso A (Opposite.unop Vop)).hom.appTop ≫
                ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ
                  (Opposite.unop Vop).1).topIso.hom) =
          ((AlgebraicGeometry.Scheme.ΓSpecIso
              (CommRingCat.of (A.sectionsRing (Opposite.unop Uop).1))).inv ≫
            (AlgebraicGeometry.Scheme.relativeSpec.affineIso A (Opposite.unop Uop)).hom.appTop ≫
              ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ
                (Opposite.unop Uop).1).topIso.hom) ≫
            (AlgebraicGeometry.Scheme.relativeSpec A).left.presheaf.map
              (CategoryTheory.homOfLE hpre).op
        rw [AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality_assoc,
          CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, happ2] }


/-- The ring homomorphism `A(U) → Γ(Spec_X A, π⁻¹U) → Γ(T, h⁻¹π⁻¹U) = Γ(T, g⁻¹U)` on an open `U` given by an
`X`-morphism `h : T → Spec_X A` (`structureRingMap`, the sheaf map of `h`, the identity `h ≫ π = g`). -/

noncomputable def AlgebraicGeometry.Scheme.relativeSpec.pullbackSections {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A)
    (U : X.Opens) : A.sectionsRing U →+* Γ(T.left, T.hom ⁻¹ᵁ U) :=
  ((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op U) ≫
    h.left.app ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) ≫
    T.left.presheaf.map (CategoryTheory.eqToHom
      (show T.hom ⁻¹ᵁ U = h.left ⁻¹ᵁ ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) by
        rw [← CategoryTheory.Over.w h]; rfl)).op).hom

/- Naturality of `pullbackSections` in restriction: the three factors (naturality of `structureRingMap`,
   naturality of the sheaf map of `h.left`, functoriality of the `eqToHom` part) are handled one by one; the
   last two together are Mathlib's `Hom.appLE` calculus (`Scheme.Hom.map_appLE`, `Scheme.Hom.appLE_map`). -/

set_option backward.isDefEq.respectTransparency false in
theorem AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_naturality
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (T : CategoryTheory.Over X)
    (h : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A) {U V : X.Opens} (hVU : V ≤ U) :
    A.ringPresheaf.map (CategoryTheory.homOfLE hVU).op ≫
        CommRingCat.ofHom (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h V) =
      CommRingCat.ofHom (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U) ≫
        T.left.presheaf.map (CategoryTheory.homOfLE (T.hom.preimage_mono hVU)).op := by
  have hpre : (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ V ≤
      (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U :=
    (AlgebraicGeometry.Scheme.relativeSpec A).hom.preimage_mono hVU
  have hnat : A.ringPresheaf.map (CategoryTheory.homOfLE hVU).op ≫
      (AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op V) =
      (AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op U) ≫
        (AlgebraicGeometry.Scheme.relativeSpec A).left.presheaf.map
          (CategoryTheory.homOfLE hpre).op :=
    (AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).naturality
      (CategoryTheory.homOfLE hVU).op
  have e1 : ∀ W : X.Opens,
      CommRingCat.ofHom (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h W) =
      (AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op W) ≫
        h.left.appLE ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ W) (T.hom ⁻¹ᵁ W)
          (le_of_eq (show T.hom ⁻¹ᵁ W =
              h.left ⁻¹ᵁ ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ W) by
            rw [← CategoryTheory.Over.w h]; rfl)) := fun _ => rfl
  rw [e1 V, e1 U, ← CategoryTheory.Category.assoc, hnat, CategoryTheory.Category.assoc,
    CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.Hom.map_appLE,
    AlgebraicGeometry.Scheme.Hom.appLE_map]


private theorem relSpecAux_topIso_inv_eq_appLE {Y : AlgebraicGeometry.Scheme.{u}} (W : Y.Opens) :
    W.topIso.inv = W.ι.appLE W ⊤ (by simp) := by
  rw [AlgebraicGeometry.Scheme.Opens.ι_appLE, AlgebraicGeometry.Scheme.Opens.topIso_inv]
  exact congrArg _ (Subsingleton.elim _ _)

private theorem relSpecAux_presheaf_map_eq_id {Y : AlgebraicGeometry.Scheme.{u}} {V : Y.Opensᵒᵖ} (f : V ⟶ V) :
    Y.presheaf.map f = CategoryTheory.CategoryStruct.id _ := by
  rw [Subsingleton.elim f (CategoryTheory.CategoryStruct.id _)]; exact Y.presheaf.map_id V

private theorem relSpecAux_spec_gamma_collapse {R S : CommRingCat.{u}} (f : R ⟶ S)
    (V : (AlgebraicGeometry.Spec R).Opens) (hV : V = ⊤)
    (h : (⊤ : (AlgebraicGeometry.Spec S).Opens) ≤ AlgebraicGeometry.Spec.map f ⁻¹ᵁ V) :
    (AlgebraicGeometry.Scheme.ΓSpecIso R).inv ≫
        (AlgebraicGeometry.Spec R).presheaf.map (CategoryTheory.eqToHom hV).op ≫
        (AlgebraicGeometry.Spec.map f).app V ≫
        (AlgebraicGeometry.Spec S).presheaf.map (CategoryTheory.homOfLE h).op ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso S).hom = f := by
  subst hV
  rw [CategoryTheory.eqToHom_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Category.id_comp,
    show (AlgebraicGeometry.Spec S).presheaf.map (CategoryTheory.homOfLE h).op =
        CategoryTheory.CategoryStruct.id _ from relSpecAux_presheaf_map_eq_id _]
  simp only [CategoryTheory.Category.id_comp,
    show AlgebraicGeometry.Scheme.Hom.app (AlgebraicGeometry.Spec.map f) ⊤ =
        (AlgebraicGeometry.Spec.map f).appTop from rfl,
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality, CategoryTheory.Iso.inv_hom_id_assoc]
  simp

private theorem relSpecAux_appLE_congr_hom {Y Z : AlgebraicGeometry.Scheme.{u}} {f g : Y ⟶ Z} (h : f = g)
    (U : Z.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V e' := by subst h; rfl

set_option backward.isDefEq.respectTransparency false in
/-- On an affine open `U`: the structure map `Γ(X,U) → A(U)` followed by `sectionsToFunctions` is the sheaf map
of `π`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.sectionsUnit_comp_sectionsToFunctions
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.affineOpens) :
    CommRingCat.ofHom (A.sectionsUnit U.1) ≫
        AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions A U =
      (AlgebraicGeometry.Scheme.relativeSpec A).hom.app U.1 := by
  -- notation
  have key : (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv ≫
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).ι ≫
        (AlgebraicGeometry.Scheme.relativeSpec A).hom =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (A.sectionsUnit U.1)) ≫ U.2.fromSpec := by
    rw [← CategoryTheory.Category.assoc,
      AlgebraicGeometry.Scheme.relativeSpec.affineIso_inv_ι A U]
    exact (AlgebraicGeometry.Scheme.AffineAlgebra.chart_hom A.toAffineAlgebra ⟨U.1, U.2⟩).trans
      (by rfl)
  have main : (AlgebraicGeometry.Scheme.relativeSpec A).hom.app U.1 ≫
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).topIso.inv ≫
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv.appTop ≫
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (A.sectionsRing U.1))).hom =
      CommRingCat.ofHom (A.sectionsUnit U.1) := by
    have e1 : (AlgebraicGeometry.Scheme.relativeSpec A).hom.app U.1 ≫
        ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).topIso.inv =
        (((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).ι ≫
          (AlgebraicGeometry.Scheme.relativeSpec A).hom).appLE U.1 ⊤ (by simp) := by
      rw [AlgebraicGeometry.Scheme.Hom.comp_appLE]
      congr 1
      exact relSpecAux_topIso_inv_eq_appLE _
    rw [← CategoryTheory.Category.assoc, e1, ← CategoryTheory.Category.assoc,
      show (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv.appTop
          = (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv.appLE ⊤ ⊤ (by simp) from
        (AlgebraicGeometry.Scheme.Hom.appLE_eq_app _).symm,
      AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE
        (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv
        (((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).ι ≫
          (AlgebraicGeometry.Scheme.relativeSpec A).hom) U.1 ⊤ ⊤ (by simp) (by simp),
      relSpecAux_appLE_congr_hom key U.1 ⊤ _ (by rw [← key]; simp),
      AlgebraicGeometry.Scheme.Hom.comp_appLE, U.2.fromSpec_app_self]
    simp only [CategoryTheory.Category.assoc]
    simp only [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.Hom.appTop,
      CategoryTheory.Category.assoc, TopologicalSpace.Opens.map_top]
    exact relSpecAux_spec_gamma_collapse (CommRingCat.ofHom (A.sectionsUnit U.1)) _
      U.2.fromSpec_preimage_self _
  rw [AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions, ← main]
  simp only [CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id_assoc]
  rw [← CategoryTheory.Category.assoc (AlgebraicGeometry.Scheme.Hom.appTop
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).inv),
    ← AlgebraicGeometry.Scheme.Hom.comp_appTop, CategoryTheory.Iso.hom_inv_id]
  simp


noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.unitPresheaf {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) : X.presheaf ⟶ A.ringPresheaf where
  app U := CommRingCat.ofHom (A.sectionsUnit U.unop)
  naturality U V f := by
    ext r
    exact _root_.PresheafOfModules.naturality_apply A.one.val f r

theorem AlgebraicGeometry.Scheme.relativeSpec.unitPresheaf_comp_structureRingMap
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) :
    A.unitPresheaf ≫ AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A =
      (AlgebraicGeometry.Scheme.relativeSpec A).hom.c := by
  refine TopCat.Sheaf.hom_ext (B := fun U : X.affineOpens => U.1) _ _
    (by rw [Subtype.range_coe]; exact X.isBasis_affineOpens) (fun U => ?_)
  rw [CategoryTheory.NatTrans.comp_app,
    AlgebraicGeometry.Scheme.relativeSpec.structureRingMap,
    TopCat.Sheaf.extend_hom_app]
  exact AlgebraicGeometry.Scheme.relativeSpec.sectionsUnit_comp_sectionsToFunctions A U


set_option backward.isDefEq.respectTransparency false in
/-- `pullbackSections` sends the structure sections `sectionsUnit U r` of `A` to the sheaf map of `T.hom`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_sectionsUnit
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (T : CategoryTheory.Over X)
    (h : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A) (U : X.Opens) (r : Γ(X, U)) :
    AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U (A.sectionsUnit U r) =
      (T.hom.app U).hom r := by
  have hU : (CommRingCat.ofHom (A.sectionsUnit U) ≫
      (AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op U)) =
      (AlgebraicGeometry.Scheme.relativeSpec A).hom.app U :=
    congrArg (fun α => CategoryTheory.NatTrans.app α (Opposite.op U))
      (AlgebraicGeometry.Scheme.relativeSpec.unitPresheaf_comp_structureRingMap A)
  have key : CommRingCat.ofHom (A.sectionsUnit U) ≫
      ((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op U) ≫
        h.left.app ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) ≫
        T.left.presheaf.map (CategoryTheory.eqToHom
          (show T.hom ⁻¹ᵁ U = h.left ⁻¹ᵁ ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) by
            rw [← CategoryTheory.Over.w h]; rfl)).op) = T.hom.app U := by
    rw [← CategoryTheory.Category.assoc, hU, ← CategoryTheory.Category.assoc,
      show T.left.presheaf.map (CategoryTheory.eqToHom
          (show T.hom ⁻¹ᵁ U = h.left ⁻¹ᵁ ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U) by
            rw [← CategoryTheory.Over.w h]; rfl)).op =
        T.left.presheaf.map (CategoryTheory.homOfLE
          (show T.hom ⁻¹ᵁ U ≤ (h.left ≫ (AlgebraicGeometry.Scheme.relativeSpec A).hom) ⁻¹ᵁ U by
            rw [CategoryTheory.Over.w h])).op from congrArg _ (Subsingleton.elim _ _)]
    exact (relSpecAux_appLE_congr_hom (CategoryTheory.Over.w h) U (T.hom ⁻¹ᵁ U) _ le_rfl).trans
      (AlgebraicGeometry.Scheme.Hom.appLE_eq_app _)
  exact congrArg (fun φ => CommRingCat.Hom.hom φ r) key


set_option backward.isDefEq.respectTransparency false in
/-- `pullbackSections` is `O_X`-linear: the image of `r • m` is `T.hom♯(r)` times the image of `m`. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_smul
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (T : CategoryTheory.Over X)
    (h : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A) (U : X.Opens)
    (r : Γ(X, U)) (m : A.sectionsRing U) :
    AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U
        (@HSMul.hSMul Γ(X, U) Γ(A.carrier, U) Γ(A.carrier, U) _ r m) =
      (T.hom.app U).hom r *
        AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U m := by
  rw [← A.smul_eq_sectionsUnit_mul U r m, map_mul,
    AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_sectionsUnit]

/-- The other direction of Stacks 01LQ: an `X`-morphism `h` ↦ the morphism of sheaves of modules `A → g_*O_T`
given on each open by the additive part of `pullbackSections`; `O_X`-linearity and naturality in restriction
are proved above. -/

noncomputable def AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A) :
    A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
      (SheafOfModules.unit T.left.ringCatSheaf) :=
  ⟨_root_.PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U.unop).toAddMonoidHom
      naturality := by
        intro Uop Vop f
        have hVU : (Opposite.unop Vop : X.Opens) ≤ (Opposite.unop Uop : X.Opens) :=
          CategoryTheory.leOfHom f.unop
        have key := AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_naturality A T h hVU
        ext a
        exact congrArg (fun φ => φ.hom a) key }
    (fun U r m =>
      AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_smul A T h U.unop r m)⟩


/- Lemmas needed to show that the two directions of Stacks 01LQ are inverse to each other. -/

/-- On an affine open, the component of `structureRingMap` is `sectionsToFunctions` (the computation rule of
`restrictHomEquivHom`). -/

theorem AlgebraicGeometry.Scheme.relativeSpec.structureRingMap_app_affine
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.affineOpens) :
    (AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op U.1) =
      AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions A U :=
  TopCat.Sheaf.extend_hom_app (B := fun U : X.affineOpens => U.1) _ _ _ _ U

/-- `π⁻¹U` is affine; the counit of `Γ ⊣ Spec` gives `π⁻¹U → Spec Γ(π⁻¹U) → Spec A(U)`, which is `affineIso`. -/

@[reassoc]
theorem AlgebraicGeometry.Scheme.relativeSpec.toSpecΓ_specMap_sectionsToFunctions
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.affineOpens) :
    ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).toSpecΓ ≫
        AlgebraicGeometry.Spec.map
          (AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions A U) =
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).hom := by
  have hstf : AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions A U ≫
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1).topIso.inv =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (A.sectionsRing U.1))).inv ≫
        (AlgebraicGeometry.Scheme.relativeSpec.affineIso A U).hom.appTop := by
    rw [AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions,
      CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
      CategoryTheory.Iso.hom_inv_id, CategoryTheory.Category.comp_id]
  rw [AlgebraicGeometry.Scheme.Opens.toSpecΓ, CategoryTheory.Category.assoc,
    ← AlgebraicGeometry.Spec.map_comp, hstf, AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Scheme.toSpecΓ_naturality_assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, CategoryTheory.Category.comp_id]


/-- `Γ ⊣ Spec`: a morphism `V ⟶ Spec R` is determined by the ring homomorphism `R ⟶ Γ(Y,V)` (`toSpecΓ` is the unit
of the adjunction). -/

theorem AlgebraicGeometry.Scheme.Opens.toSpecΓ_specMap_injective
    {Y : AlgebraicGeometry.Scheme.{u}} (V : Y.Opens) {R : CommRingCat.{u}}
    {γ₁ γ₂ : R ⟶ Γ(Y, V)}
    (he : V.toSpecΓ ≫ AlgebraicGeometry.Spec.map γ₁ =
      V.toSpecΓ ≫ AlgebraicGeometry.Spec.map γ₂) : γ₁ = γ₂ := by
  have h1 := congrArg AlgebraicGeometry.Scheme.Hom.appTop he
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop,
    AlgebraicGeometry.Scheme.Opens.toSpecΓ_appTop,
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality_assoc] at h1
  rwa [CategoryTheory.cancel_epi, CategoryTheory.cancel_mono] at h1


/- **The key piece identity**: the construction of `ofAlgebraMap` on the affine piece `U`, with
`φ = toAlgebraMap A T h` substituted, is exactly the restriction of `h` to that piece. The left side becomes the
restriction `resLE` of `h.left` by `Opens.toSpecΓ_SpecMap_appLE`; on the right, `chart U` becomes
`affineIso.inv ≫ ι` by `affineIso_inv_ι`, and the two `affineIso`s cancel. -/

set_option backward.isDefEq.respectTransparency false in
theorem AlgebraicGeometry.Scheme.relativeSpec.toSpecΓ_specMap_pullbackSections_chart
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (T : CategoryTheory.Over X)
    (h : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A) (U : X.affineOpens) :
    (T.hom ⁻¹ᵁ U.1).toSpecΓ ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U.1)) ≫
        A.toAffineAlgebra.chart ⟨U.1, U.2⟩ =
      (T.hom ⁻¹ᵁ U.1).ι ≫ h.left := by
  have e1 : CommRingCat.ofHom
        (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U.1) =
      AlgebraicGeometry.Scheme.relativeSpec.sectionsToFunctions A U ≫
        h.left.appLE ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1)
          (T.hom ⁻¹ᵁ U.1)
          (le_of_eq (show T.hom ⁻¹ᵁ U.1 =
              h.left ⁻¹ᵁ ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ U.1) by
            rw [← CategoryTheory.Over.w h]; rfl)) := by
    rw [← AlgebraicGeometry.Scheme.relativeSpec.structureRingMap_app_affine A U]
    rfl
  rw [e1, AlgebraicGeometry.Spec.map_comp, CategoryTheory.Category.assoc,
    AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
    AlgebraicGeometry.Scheme.relativeSpec.toSpecΓ_specMap_sectionsToFunctions_assoc,
    ← AlgebraicGeometry.Scheme.relativeSpec.affineIso_inv_ι A U,
    CategoryTheory.Iso.hom_inv_id_assoc, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]



/-- The computation rule of `ofAlgebraMap` on each piece (the `ι_` lemma of
`glueMorphismsOverOfLocallyDirected`). -/

theorem AlgebraicGeometry.Scheme.relativeSpec.ι_ofAlgebraMap_left
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (T : CategoryTheory.Over X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
      (SheafOfModules.unit T.left.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward T.hom φ) (U : X.AffineZariskiSite) :
    (T.hom ⁻¹ᵁ U.toOpens).ι ≫
        (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap A T φ hφ).left =
      (T.hom ⁻¹ᵁ U.toOpens).toSpecΓ ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (A.algebraMapSections T.hom φ hφ U.toOpens)) ≫
        A.toAffineAlgebra.chart U :=
  AlgebraicGeometry.Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left
    (AlgebraicGeometry.Scheme.preimageAffineCover T.hom)
    (fun U => (T.hom ⁻¹ᵁ U.toOpens).toSpecΓ ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (A.algebraMapSections T.hom φ hφ U.toOpens)) ≫
      A.toAffineAlgebra.chart U)
    (fun {_ _} hij => A.chartMap_restrict T.hom φ hφ (CategoryTheory.leOfHom hij))
    (fun U => A.chart_comp_relativeSpec_hom T.hom φ hφ U) U

/-- The section ring homomorphisms of the two directions on opens, as morphisms of presheaves of rings into the
sheaf `U ↦ Γ(T, g⁻¹U)`. `right_inv` lifts "equal on affine opens" to "equal on all opens" through these two
and `TopCat.Sheaf.hom_ext`. -/

noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.algebraMapNatTrans
    {X T' : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (g : T' ⟶ X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward g).obj
      (SheafOfModules.unit T'.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward g φ) :
    A.ringPresheaf ⟶
      ((TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj T'.sheaf).obj where
  app U := CommRingCat.ofHom (A.algebraMapSections g φ hφ U.unop)
  naturality _ _ f :=
    (A.algebraMapSections_naturality g φ hφ (CategoryTheory.leOfHom f.unop)).symm

noncomputable def AlgebraicGeometry.Scheme.relativeSpec.pullbackNatTrans
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (T : CategoryTheory.Over X)
    (h : T ⟶ AlgebraicGeometry.Scheme.relativeSpec A) :
    A.ringPresheaf ⟶
      ((TopCat.Sheaf.pushforward CommRingCat.{u} T.hom.base).obj T.left.sheaf).obj where
  app U := CommRingCat.ofHom
    (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U.unop)
  naturality _ _ f :=
    AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_naturality A T h
      (CategoryTheory.leOfHom f.unop)

/-- `toAlgebraMap ∘ ofAlgebraMap = id` on affine opens: the piece constructions of both sides give the same
`V ⟶ Spec_X A`; `chart U` is a monomorphism and `toSpecΓ ≫ Spec.map (-)` is injective, so the two ring
homomorphisms agree. -/

theorem AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_ofAlgebraMap_affine
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (T : CategoryTheory.Over X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
      (SheafOfModules.unit T.left.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward T.hom φ) (U : X.affineOpens) :
    CommRingCat.ofHom (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T
        (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap A T φ hφ) U.1) =
      CommRingCat.ofHom (A.algebraMapSections T.hom φ hφ U.1) := by
  refine AlgebraicGeometry.Scheme.Opens.toSpecΓ_specMap_injective (T.hom ⁻¹ᵁ U.1) ?_
  have h1 := AlgebraicGeometry.Scheme.relativeSpec.toSpecΓ_specMap_pullbackSections_chart
    A T (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap A T φ hφ) U
  rw [AlgebraicGeometry.Scheme.relativeSpec.ι_ofAlgebraMap_left A T φ hφ ⟨U.1, U.2⟩] at h1
  have h2 := (CategoryTheory.Category.assoc _ _ _).trans
    (h1.trans (CategoryTheory.Category.assoc _ _ _).symm)
  have hoi : AlgebraicGeometry.IsOpenImmersion (A.toAffineAlgebra.chart ⟨U.1, U.2⟩) :=
    AlgebraicGeometry.Scheme.AffineAlgebra.chart_isOpenImmersion A.toAffineAlgebra ⟨U.1, U.2⟩
  have : CategoryTheory.Mono (A.toAffineAlgebra.chart ⟨U.1, U.2⟩) :=
    @AlgebraicGeometry.IsOpenImmersion.mono _ _ _ hoi
  exact (CategoryTheory.cancel_mono (A.toAffineAlgebra.chart ⟨U.1, U.2⟩)).mp h2

/-- Extended to all opens by the uniqueness of extension from a basis for sheaves. -/

theorem AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_ofAlgebraMap
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (T : CategoryTheory.Over X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
      (SheafOfModules.unit T.left.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward T.hom φ) (U : X.Opens) :
    CommRingCat.ofHom (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T
        (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap A T φ hφ) U) =
      CommRingCat.ofHom (A.algebraMapSections T.hom φ hφ U) := by
  have key : AlgebraicGeometry.Scheme.relativeSpec.pullbackNatTrans A T
        (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap A T φ hφ) =
      A.algebraMapNatTrans T.hom φ hφ :=
    TopCat.Sheaf.hom_ext (B := fun U : X.affineOpens => U.1) _ _
      (by rw [Subtype.range_coe]; exact X.isBasis_affineOpens)
      (fun i => AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_ofAlgebraMap_affine
        A T φ hφ i)
  exact congrArg (fun α => α.app (Opposite.op U)) key


/-- Stacks 01LQ: `Hom_X(T, Spec_X A) ≃ {O_X-algebra maps A → g_*O_T}`. Both directions are the explicit
constructions above. -/
noncomputable def AlgebraicGeometry.Scheme.relativeSpecHomEquiv {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (T : CategoryTheory.Over X) :
    (T ⟶ AlgebraicGeometry.Scheme.relativeSpec A) ≃
      { φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
            (SheafOfModules.unit T.left.ringCatSheaf) //
        A.IsAlgebraMapToPushforward T.hom φ } where
  toFun h := ⟨AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap A T h,
    ⟨fun U a b => map_mul (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U)
        (show A.sectionsRing U from a) (show A.sectionsRing U from b),
     fun U => map_one (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections A T h U)⟩⟩
  invFun φ := AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap A T φ.1 φ.2
  left_inv := by
    intro h
    refine CategoryTheory.Over.OverMorphism.ext ?_
    refine AlgebraicGeometry.Scheme.Cover.hom_ext
      (AlgebraicGeometry.Scheme.preimageAffineCover T.hom) _ _ (fun U => ?_)
    exact (AlgebraicGeometry.Scheme.relativeSpec.ι_ofAlgebraMap_left A T _ _ U).trans
      (AlgebraicGeometry.Scheme.relativeSpec.toSpecΓ_specMap_pullbackSections_chart
        A T h ⟨U.toOpens, U.2⟩)
  right_inv := by
    intro φ
    refine Subtype.ext ?_
    refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ (fun U => ?_)
    ext a
    exact congrArg (fun ψ : CommRingCat.of (A.sectionsRing U) ⟶
        CommRingCat.of Γ(T.left, T.hom ⁻¹ᵁ U) => ψ.hom a)
      (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_ofAlgebraMap A T φ.1 φ.2 U)

end
