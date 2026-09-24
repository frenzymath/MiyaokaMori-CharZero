import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseGradedModel
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseDegreeOne
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseLiftRestrict
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.TotLineAffineOverBaseProjRangeOfKernel
import MiyaokaMori.RingTheory.SymmetricAlgebraSplitKernel
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleLineSection
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualCurryMap
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackIdMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion

/-! # The local piece of the `L`-section on a chart, and `V₊(T) ⊆ σ_L(W)`

Used for `totalSpace.mem_range_lSection_of_not_mem_basicOpen_oCoordinate` (`TotLineAffineOverBase`; in the paper,
"the subbundle `L ↪ O ⊕ L` defines a section of `P(O ⊕ L)` whose complement is naturally `Tot(L)`"; Stacks 01O4,
01M9).

Notation: `V = O ⊕ L`, `W ⊆ X` affine inside an open `U₂` trivialising `L^∨` (`e₂ : L^∨|_{U₂} ≅ O`),
`R = Γ(W, O)`, `A(W) = ⊕_m Γ(W, Sym^m V^∨)`, `N = Γ(W, L^∨)`, `ε : O^∨ ≅ O` (in the main file `ε = unitDualIso X`, so
that `T := genSections (oFunctional ε W) = DirectSum.of 1 (oCoordinate L W)` is the `O`-coordinate).
`lSection L = projBundle.lift V 𝟙 L^∨ (lSection.quotientMap L)`, and `(U₂, e₂, V₂ := W)` is an admissible piece for it
(`W ≤ U₂ ⊓ 𝟙⁻¹W`), with local ring homomorphism
`ψ = lSectionPiece : A(W) → Γ(W, O_W)`, `ψ = res ∘ localRingHom V 𝟙 L^∨ (lSection.quotientMap L) U₂ e₂ W`.

## Contents
* `lSectionPiece_sectionsUnitHom`: `ψ(sectionsUnitHom r) = r` (degree zero is the identity of `R`, read through
  `Opens.topIso`; `localRingHom_sectionsUnit`).
* `lSectionPiece_genSections_sLinear`: on the degree-one generators `s(n) = (snd)^∨ n`, `n ∈ N`,
  `ψ(genSections (s n)) = res (Θ (n|_{W}))` where `Θ : g^*(L^∨) ≅ O_W` is the trivialization `e₂` transported to the
  piece (`localRingHomComponent_one_symGen_apply`, `pullbackId`, `dualCurryMap_snd_comp_inr`); hence
  `n ↦ ψ(genSections (s n))` is a **bijection** `N → Γ(W, O_W)` (`lSectionPiece_genSections_sLinear_bijective`):
  restriction of sections along `W = U₂ ⊓ W`, an isomorphism of sheaves, and the identification `Γ(W, O_W) = Γ(X, W)`.
* `mem_range_lSection_of_not_mem_basicOpen_genSections_oFunctional`: **`V₊(T) ⊆ σ_L(W)`** — a point `q` of
  `Proj A(W)` outside `D₊(T)`, moved to `P(O ⊕ L)` through `π⁻¹W ≅ Proj A(W)`, is in the image of `lSection L`.
  Proof: `W.ι ≫ lSection L = fromOfGlobalSections ψ ≫ affineIso⁻¹ ≫ ι` (`projBundle.lift_restrict`), and
  `q ∈ range (fromOfGlobalSections ψ)` by `Proj.mem_range_fromOfGlobalSections_of_forall_mem_span`
  (`TotLineAffineOverBaseProjRangeOfKernel`) with `s := genSections (s λ)`, `λ` the preimage of `1` under the
  bijection above (`ψ s = 1`), degree zero onto by the first item, and `ker ψ ∩ A(W)_k ⊆ (T)` by the polynomial model
  `A(W) ≅ Sym_R(R·T ⊕ N)`, `N ≅ R` (`SymmetricAlgebra.ModuleSplitting.mem_span_ι_T_of_mem_symmetricPiece_of_eq_zero`,
  `TotLineAffineOverBaseSymSplitKernel`, transported along `symLiftHom`).
  The hypothesis `ψ(T) = 0` is taken as an argument (`hT0`); in the main file it is
  `localRingHom_lSection_oCoordinate_eq_zero`.

Edge cases: `W = ∅` (no points; all rings zero). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Restriction maps of the structure sheaf between two opens each contained in the other are bijective. -/
theorem presheaf_map_bijective_of_le_of_le {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  refine Function.bijective_iff_has_inverse.mpr ⟨(X.presheaf.map (homOfLE h').op).hom, fun x => ?_, fun y => ?_⟩
  · rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
    have : (homOfLE h).op ≫ (homOfLE h').op = 𝟙 (op V) := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    rfl
  · rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
    have : (homOfLE h').op ≫ (homOfLE h).op = 𝟙 (op U) := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    rfl

/-- Restriction maps of a sheaf of modules between two opens each contained in the other are bijective. -/
theorem module_presheaf_map_bijective_of_le_of_le (M : X.Modules) {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    Function.Bijective (M.presheaf.map (homOfLE h).op) :=
  Function.bijective_iff_has_inverse.mpr ⟨M.presheaf.map (homOfLE h').op,
    fun x => map_homOfLE_map_homOfLE_self M h h' x, fun y => map_homOfLE_map_homOfLE_self M h' h y⟩

/-- The section map of an isomorphism of sheaves of modules is bijective. -/
theorem bijective_app_of_isIso {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] (U : X.Opens) :
    Function.Bijective (φ.app U) :=
  Function.bijective_iff_has_inverse.mpr ⟨(asIso φ).inv.app U,
    fun x => modIso_inv_app_hom_app (asIso φ) U x, fun y => modIso_hom_app_inv_app (asIso φ) U y⟩

/-- Section maps of module morphisms commute with restriction. -/
theorem app_restrict {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.totalSpace

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.projBundle

variable {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]
  (U₂ : X.Opens) (e₂ : (dual L).restrict U₂.ι ≅ SheafOfModules.unit U₂.toScheme.ringCatSheaf)
  (W : X.affineOpens)

/-- `W ≤ U₂ ⊓ 𝟙⁻¹W`: the admissibility of the piece `(U₂, e₂, V₂ := W)` of `lSection L`. -/
theorem lSectionPiece_le (hW : W.1 ≤ U₂) : W.1 ≤ U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1 :=
  le_inf hW le_rfl

/-- `U₂ ⊓ 𝟙⁻¹W ≤ W`. -/
theorem lSectionPiece_ge : U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1 ≤ W.1 := inf_le_right

/-- **The local piece `ψ` of the `L`-section on the chart `W`**: the ring homomorphism
`A(W) → Γ(W, O_W)` of the admissible piece `(U₂, e₂, V₂ := W)` of `lSection L = projBundle.lift V 𝟙 L^∨ (quotientMap)`
(the ring homomorphism inside `projBundle.liftLocal`). -/
def lSectionPiece (hW : W.1 ≤ U₂) :
    (symGradedAlgebra (dual (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsRing
        W.1 →+* Γ(W.1.toScheme, ⊤) :=
  (X.homOfLE (lSectionPiece_le U₂ W hW)).appTop.hom.comp
    (localRingHom (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
      (CategoryTheory.CategoryStruct.id X) (dual L) (lSection.quotientMap L) U₂ e₂ W.1)

/-- **`ψ` in degree zero is the identity of `R`** (through `Opens.topIso : Γ(W, O_W) ≅ Γ(X, W)`):
`localRingHom_sectionsUnit` gives the restriction along `g = ι ≫ 𝟙 : U₂ ⊓ W → X`, and all the maps involved are
restriction maps of `O_X` between the same opens. -/
theorem lSectionPiece_sectionsUnitHom (hW : W.1 ≤ U₂) (r : Γ(X, W.1)) :
    lSectionPiece L U₂ e₂ W hW
        ((symGradedAlgebra (dual (biprod (C := X.Modules)
          (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsUnitHom W.1 r) =
      W.1.topIso.inv.hom r := by
  show (X.homOfLE (lSectionPiece_le U₂ W hW)).appTop.hom
    (localRingHom _ (CategoryTheory.CategoryStruct.id X) _ (lSection.quotientMap L) U₂ e₂ W.1
      ((symGradedAlgebra (dual _)).sectionsUnit W.1 r).1) = _
  rw [localRingHom_sectionsUnit]
  unfold localRingHomBase localRingHomIncl
  have hid : (((CategoryTheory.CategoryStruct.id X).app W.1).hom r : Γ(X, (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1)) =
    r := rfl
  rw [Hom.comp_appLE, Hom.comp_appLE, CommRingCat.comp_apply, hid, Scheme.Opens.ι_app, Scheme.homOfLE_appLE,
    Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  rw [CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun k => (X.presheaf.map k).hom r) (Subsingleton.elim _ _)

/-- `r ↦ ψ(sectionsUnitHom r)` is a bijection `Γ(X, W) → Γ(W, O_W)`. -/
theorem lSectionPiece_sectionsUnitHom_bijective (hW : W.1 ≤ U₂) :
    Function.Bijective (fun r : Γ(X, W.1) => lSectionPiece L U₂ e₂ W hW
      ((symGradedAlgebra (dual (biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsUnitHom W.1 r)) := by
  have h : (fun r : Γ(X, W.1) => lSectionPiece L U₂ e₂ W hW
      ((symGradedAlgebra (dual (biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsUnitHom W.1 r)) =
      W.1.topIso.inv.hom := funext (lSectionPiece_sectionsUnitHom L U₂ e₂ W hW)
  rw [h]
  exact (ConcreteCategory.isIso_iff_bijective _).mp (Iso.isIso_inv _)

/-- The trivialization `e₂` transported to the piece: `Θ : g^*(L^∨) ⟶ O_{U₂ ⊓ W}`, `g = ι ≫ 𝟙`,
`Θ = pullbackComp⁻¹ ≫ ι^*(pullbackId) ≫ e'` (an isomorphism). -/
def lSectionPieceTriv :
    (Modules.pullback (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1)).obj (dual L) ⟶
      SheafOfModules.unit (U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1).toScheme.ringCatSheaf :=
  (pullbackComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U₂ W.1)
      (CategoryTheory.CategoryStruct.id X)).inv.app (dual L) ≫
    (Modules.pullback (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U₂ W.1)).map
      ((pullbackId X).hom.app (dual L)) ≫
    (localRingHomTriv (CategoryTheory.CategoryStruct.id X) (dual L) U₂ e₂ W.1).hom

/-- `Θ` as an isomorphism (its `hom` is definitionally `lSectionPieceTriv`). -/
def lSectionPieceTrivIso :
    (Modules.pullback (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1)).obj (dual L) ≅
      SheafOfModules.unit (U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1).toScheme.ringCatSheaf :=
  ((pullbackComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U₂ W.1)
      (CategoryTheory.CategoryStruct.id X)).app (dual L)).symm ≪≫
    ((Modules.pullback (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U₂ W.1)).mapIso
      ((pullbackId X).app (dual L)) ≪≫
    localRingHomTriv (CategoryTheory.CategoryStruct.id X) (dual L) U₂ e₂ W.1)

omit [L.IsLineBundle] in
theorem lSectionPieceTrivIso_hom : (lSectionPieceTrivIso L U₂ e₂ W).hom = lSectionPieceTriv L U₂ e₂ W := rfl

omit [L.IsLineBundle] in
theorem lSectionPiece_triv_isIso_aux : IsIso (lSectionPieceTriv L U₂ e₂ W) := by
  rw [← lSectionPieceTrivIso_hom]
  infer_instance

/-- `𝟙^*((snd)^∨) ≫ lSection.quotientMap L = (pullbackId X).hom.app L^∨` (`(snd)^∨ ≫ (inr)^∨ = 𝟙`). -/
theorem pullback_map_sLinear_comp_quotientMap :
    (Modules.pullback (CategoryTheory.CategoryStruct.id X)).map
        (dualCurryMap (biprod.snd (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
          (Y := L))) ≫ lSection.quotientMap L =
      (pullbackId X).hom.app (dual L) := by
  unfold AlgebraicGeometry.Scheme.lSection.quotientMap
  rw [← Category.assoc, (pullbackId X).hom.naturality, Category.assoc, CategoryTheory.Functor.id_map, dualMap_eq]
  exact (congrArg (fun k => (pullbackId X).hom.app (dual L) ≫ k)
    (dualCurryMap_snd_comp_inr (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)).trans (Category.comp_id _)

/-- `g^*((snd)^∨) ≫ (pullbackComp⁻¹ ≫ ι^*(quotientMap) ≫ e') = Θ`. -/
theorem pullback_map_sLinear_comp_sheafHom :
    (Modules.pullback (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1)).map
        (dualCurryMap (biprod.snd (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
          (Y := L))) ≫
      ((pullbackComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U₂ W.1)
          (CategoryTheory.CategoryStruct.id X)).inv.app _ ≫
        (Modules.pullback (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U₂ W.1)).map
          (lSection.quotientMap L) ≫
        (localRingHomTriv (CategoryTheory.CategoryStruct.id X) (dual L) U₂ e₂ W.1).hom) =
      lSectionPieceTriv L U₂ e₂ W := by
  unfold lSectionPieceTriv localRingHomBase
  rw [← Category.assoc, (pullbackComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U₂ W.1)
      (CategoryTheory.CategoryStruct.id X)).inv.naturality, Category.assoc, CategoryTheory.Functor.comp_map,
    ← Category.assoc ((Modules.pullback (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U₂ W.1)).map _),
    ← CategoryTheory.Functor.map_comp, pullback_map_sLinear_comp_quotientMap]

/-- **`ψ` on the degree-one generators `s(n)`, `n ∈ Γ(W, L^∨)`**: `ψ(genSections (s n)) = res(Θ(n|_{U₂ ⊓ W}))`
(`localRingHomComponent_one_symGen_apply`, then `(snd)^∨ ≫ (inr)^∨ = 𝟙` under the adjunction). -/
theorem lSectionPiece_genSections_sLinear (hW : W.1 ≤ U₂) (n : Γ(dual L, W.1)) :
    lSectionPiece L U₂ e₂ W hW (symGradedAlgebra.genSections _ W.1 (sLinear L W.1 n)) =
      (X.homOfLE (lSectionPiece_le U₂ W hW)).appTop.hom
        (((AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit
            (U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1).toScheme.ringCatSheaf)).map
            (homOfLE (localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U₂ W.1)).op).hom
          ((lSectionPieceTriv L U₂ e₂ W).app (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1 ⁻¹ᵁ W.1)
            (((pullbackPushforwardAdjunction (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1)).unit.app
              (dual L)).app W.1 n))) := by
  show (X.homOfLE (lSectionPiece_le U₂ W hW)).appTop.hom
    (localRingHom _ (CategoryTheory.CategoryStruct.id X) _ (lSection.quotientMap L) U₂ e₂ W.1
      (DirectSum.of _ 1 (((symGen (dual _)).val.app (op W.1)).hom (sLinear L W.1 n)))) = _
  unfold localRingHom
  erw [DirectSum.toSemiring_of]
  rw [localRingHomComponent_one_symGen_apply]
  congr 1
  congr 1
  have h1 := Adjunction.homEquiv_naturality_left
    (pullbackPushforwardAdjunction (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1))
    (dualCurryMap (biprod.snd (C := X.Modules) (X := show X.Modules from SheafOfModules.unit X.ringCatSheaf)
      (Y := L)))
    ((pullbackComp (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U₂ W.1)
        (CategoryTheory.CategoryStruct.id X)).inv.app _ ≫
      (Modules.pullback (localRingHomIncl (CategoryTheory.CategoryStruct.id X) U₂ W.1)).map
        (lSection.quotientMap L) ≫
      (localRingHomTriv (CategoryTheory.CategoryStruct.id X) (dual L) U₂ e₂ W.1).hom)
  rw [pullback_map_sLinear_comp_sheafHom, Adjunction.homEquiv_unit] at h1
  have h2 := congrArg (fun k => (k.val.app (op W.1)).hom n) h1
  exact h2.symm

/-- The base morphism `g = ι ≫ 𝟙 : U₂ ⊓ 𝟙⁻¹W → X` of the piece is an open immersion. -/
theorem lSectionPiece_base_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1) := by
  unfold localRingHomBase localRingHomIncl
  infer_instance

set_option linter.style.haveILetI false in
/-- The image of the base morphism `g` is contained in `W`. -/
theorem lSectionPiece_base_image_top_le :
    haveI := lSectionPiece_base_isOpenImmersion U₂ W
    (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1) ''ᵁ ⊤ ≤ W.1 := by
  have := lSectionPiece_base_isOpenImmersion U₂ W
  rw [Scheme.Hom.image_top_eq_opensRange]
  rintro x ⟨y, rfl⟩
  exact localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U₂ W.1 (Set.mem_univ y)

set_option linter.style.haveILetI false in
/-- `W` is contained in the image of the base morphism `g` (as `W ≤ U₂ ⊓ 𝟙⁻¹W`). -/
theorem lSectionPiece_le_base_image_top (hW : W.1 ≤ U₂) :
    haveI := lSectionPiece_base_isOpenImmersion U₂ W
    W.1 ≤ (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1) ''ᵁ ⊤ := by
  have := lSectionPiece_base_isOpenImmersion U₂ W
  rw [Scheme.Hom.image_top_eq_opensRange]
  intro x hx
  refine ⟨⟨x, lSectionPiece_le U₂ W hW hx⟩, ?_⟩
  show ((X.homOfLE (inf_le_left : U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1 ≤ U₂) ≫ U₂.ι) ≫
    CategoryTheory.CategoryStruct.id X).base ⟨x, lSectionPiece_le U₂ W hW hx⟩ = x
  rw [Category.comp_id, Scheme.homOfLE_ι]
  rfl

/-- The restriction `Γ(U₂ ⊓ W, O) → Γ(W, O)` along `W ≤ U₂ ⊓ W` is bijective (`U₂ ⊓ W = W`). -/
theorem lSectionPiece_homOfLE_appTop_bijective (hW : W.1 ≤ U₂) :
    Function.Bijective (X.homOfLE (lSectionPiece_le U₂ W hW)).appTop.hom := by
  rw [Scheme.homOfLE_appTop]
  refine presheaf_map_bijective_of_le_of_le _ ?_
  show (U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1).ι ''ᵁ ⊤ ≤ W.1.ι ''ᵁ ⊤
  rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top]
  exact lSectionPiece_ge U₂ W

omit [L.IsLineBundle] in
/-- The "pull back along `g` and restrict to `⊤`" map `Γ(W, L^∨) → Γ(U₂ ⊓ W, g^*L^∨)` is bijective:
it is the restriction to the image `g ''ᵁ ⊤ = W` followed by the isomorphism `restrictFunctorIsoPullback`
(`restrictFunctorIsoPullback_hom_app_apply`). -/
theorem lSectionPiece_pullbackSectionsOn_bijective (hW : W.1 ≤ U₂) :
    Function.Bijective (pullbackSectionsOn (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1) (dual L) W.1
      ⊤ (localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U₂ W.1)) := by
  have := lSectionPiece_base_isOpenImmersion U₂ W
  have himg := lSectionPiece_base_image_top_le U₂ W
  have himg' := lSectionPiece_le_base_image_top U₂ W hW
  have hfa : (pullbackSectionsOn (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1) (dual L) W.1 ⊤
      (localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U₂ W.1) :
        Γ(dual L, W.1) → Γ((Modules.pullback (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1)).obj
          (dual L), ⊤)) =
      ((restrictFunctorIsoPullback (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1)).app
        (dual L)).hom.app ⊤ ∘ (dual L).presheaf.map (homOfLE himg).op := by
    funext n
    simp only [Function.comp]
    rw [restrictFunctorIsoPullback_hom_app_apply]
    have := pullbackSectionsOn_restrict (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1) (dual L)
      (localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U₂ W.1)
      (le_of_eq ((localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1).preimage_image_eq ⊤).symm) himg
      le_rfl n
    have hid : ((Modules.pullback (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1)).obj
        (dual L)).presheaf.map (homOfLE (le_refl (⊤ : (U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1).toScheme.Opens))).op
          (pullbackSectionsOn (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1) (dual L) W.1 ⊤
            (localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U₂ W.1) n) =
        pullbackSectionsOn (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1) (dual L) W.1 ⊤
          (localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U₂ W.1) n := by
      rw [show (homOfLE (le_refl (⊤ : (U₂ ⊓ (CategoryTheory.CategoryStruct.id X) ⁻¹ᵁ W.1).toScheme.Opens))) = 𝟙 _
        from rfl, op_id, CategoryTheory.Functor.map_id]
      rfl
    rw [hid] at this
    exact this
  rw [hfa]
  exact (bijective_app_of_isIso _ ⊤).comp (module_presheaf_map_bijective_of_le_of_le (dual L) himg himg')

/-- **The degree-one generator values of `ψ` on `Γ(W, L^∨)` form a bijection onto `Γ(W, O_W)`**: the composite of
the restriction `Γ(W, L^∨) → Γ(U₂ ⊓ W, g^*L^∨)` (bijective: `U₂ ⊓ W = W`, `restrictFunctorIsoPullback`), the
isomorphism `Θ`, and the restriction `Γ(U₂ ⊓ W, O) → Γ(W, O)` (bijective: `U₂ ⊓ W = W`). -/
theorem lSectionPiece_genSections_sLinear_bijective (hW : W.1 ≤ U₂) :
    Function.Bijective (fun n : Γ(dual L, W.1) =>
      lSectionPiece L U₂ e₂ W hW (symGradedAlgebra.genSections _ W.1 (sLinear L W.1 n))) := by
  have hfun : (fun n : Γ(dual L, W.1) =>
      lSectionPiece L U₂ e₂ W hW (symGradedAlgebra.genSections _ W.1 (sLinear L W.1 n))) =
      (X.homOfLE (lSectionPiece_le U₂ W hW)).appTop.hom ∘ (lSectionPieceTriv L U₂ e₂ W).app ⊤ ∘
        pullbackSectionsOn (localRingHomBase (CategoryTheory.CategoryStruct.id X) U₂ W.1) (dual L) W.1 ⊤
          (localRingHomBase_top_le (CategoryTheory.CategoryStruct.id X) U₂ W.1) := by
    funext n
    rw [lSectionPiece_genSections_sLinear]
    simp only [Function.comp]
    rw [pullbackSectionsOn_apply, app_restrict]
    rfl
  rw [hfun]
  have := lSectionPiece_triv_isIso_aux L U₂ e₂ W
  exact (lSectionPiece_homOfLE_appTop_bijective U₂ W hW).comp
    ((bijective_app_of_isIso (lSectionPieceTriv L U₂ e₂ W) ⊤).comp
      (lSectionPiece_pullbackSectionsOn_bijective L U₂ W hW))

section Main

variable (ε : dual (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ≅
  (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

/-- **`ψ` as an `R`-algebra homomorphism** `Sym_R Γ(W, V^∨) → Γ(W, O_W)`, for the `R`-algebra structure on
`Γ(W, O_W)` given by `r ↦ ψ(sectionsUnitHom r)` (`= topIso.inv r`). -/
theorem lSectionPiece_kernel (hW : W.1 ≤ U₂) (k : ℕ)
    (a : (symGradedAlgebra (dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsRing W.1)
    (ha : a ∈ (symGradedAlgebra (dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsGrading W.1 k)
    (hT0 : lSectionPiece L U₂ e₂ W hW (symGradedAlgebra.genSections _ W.1 (oFunctional L ε W.1)) = 0)
    (h : lSectionPiece L U₂ e₂ W hW a = 0) :
    a ∈ Ideal.span {symGradedAlgebra.genSections _ W.1 (oFunctional L ε W.1)} := by
  have := dual_biprod_isQuasicoherent L
  let _ : Algebra Γ(X, W.1) Γ(W.1.toScheme, ⊤) :=
    ((lSectionPiece L U₂ e₂ W hW).comp ((symGradedAlgebra (dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsUnitHom W.1)).toAlgebra
  let φ : SymmetricAlgebra Γ(X, W.1) Γ(dual (biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L), W.1) →ₐ[Γ(X, W.1)] Γ(W.1.toScheme, ⊤) :=
    { toRingHom := (lSectionPiece L U₂ e₂ W hW).comp (symGradedAlgebra.symLiftHom _ W.1)
      commutes' := fun r => by
        show lSectionPiece L U₂ e₂ W hW (symGradedAlgebra.symLiftHom _ W.1 (algebraMap _ _ r)) = _
        rw [symGradedAlgebra.symLiftHom_algebraMap]
        rfl }
  have hφ : ∀ b, φ b = lSectionPiece L U₂ e₂ W hW (symGradedAlgebra.symLiftHom _ W.1 b) := fun b => rfl
  have hbij : Function.Bijective (algebraMap Γ(X, W.1) Γ(W.1.toScheme, ⊤)) :=
    lSectionPiece_sectionsUnitHom_bijective L U₂ e₂ W hW
  have hev : Function.Bijective fun n : Γ(dual L, W.1) =>
      φ (SymmetricAlgebra.ι _ _ ((sectionsSplitting L ε W.1).s n)) := by
    have : (fun n : Γ(dual L, W.1) => φ (SymmetricAlgebra.ι _ _ ((sectionsSplitting L ε W.1).s n))) =
        fun n => lSectionPiece L U₂ e₂ W hW (symGradedAlgebra.genSections _ W.1 (sLinear L W.1 n)) := by
      funext n
      rw [hφ, symGradedAlgebra.symLiftHom_ι]
      rfl
    rw [this]
    exact lSectionPiece_genSections_sLinear_bijective L U₂ e₂ W hW
  have hT : φ (SymmetricAlgebra.ι _ _ (sectionsSplitting L ε W.1).T) = 0 := by
    rw [hφ, symGradedAlgebra.symLiftHom_ι]
    exact hT0
  obtain ⟨b, rfl⟩ := (symGradedAlgebra.symLiftHom_bijective _ W.2).2 a
  rw [symGradedAlgebra.symLiftHom_mem_sectionsGrading_iff _ W.1 (symGradedAlgebra.symLiftHom_bijective _ W.2).1] at ha
  have hb := (sectionsSplitting L ε W.1).mem_span_ι_T_of_mem_symmetricPiece_of_eq_zero φ hbij hev hT ha
    (by rw [hφ]; exact h)
  rw [Ideal.mem_span_singleton] at hb ⊢
  have := map_dvd (symGradedAlgebra.symLiftHom _ W.1) hb
  rwa [symGradedAlgebra.symLiftHom_ι] at this

/-- **`V₊(T) ⊆ σ_L(W)`** for `T = genSections (oFunctional ε W)` (see the module docstring). -/
theorem mem_range_lSection_of_not_mem_basicOpen_genSections_oFunctional (hW : W.1 ≤ U₂)
    (hT0 : localRingHom (biprod (C := X.Modules) (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)
      (CategoryTheory.CategoryStruct.id X) (dual L) (lSection.quotientMap L) U₂ e₂ W.1
      (symGradedAlgebra.genSections _ W.1 (oFunctional L ε W.1)) = 0)
    (q : AlgebraicGeometry.Proj ((symGradedAlgebra (dual (biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsGrading W.1))
    (hq : q ∉ AlgebraicGeometry.Proj.basicOpen ((symGradedAlgebra (dual (biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))).sectionsGrading W.1)
      (symGradedAlgebra.genSections _ W.1 (oFunctional L ε W.1))) :
    ((relativeProj.affineIso (symGradedAlgebra (dual (biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L))) W).inv ≫
      ((relativeProj (symGradedAlgebra (dual (biprod (C := X.Modules)
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) L)))).hom ⁻¹ᵁ W.1).ι).base q ∈
      Set.range (lSection L).base := by
  have hepi : CategoryTheory.Epi (lSection.quotientMap L) := lSection.quotientMap_epi L
  have : AlgebraicGeometry.IsAffine W.1.toScheme := W.2
  set ψ := lSectionPiece L U₂ e₂ W hW with hψ
  have hT0' : ψ (symGradedAlgebra.genSections _ W.1 (oFunctional L ε W.1)) = 0 := by
    show (X.homOfLE (lSectionPiece_le U₂ W hW)).appTop.hom (localRingHom _ _ _ _ U₂ e₂ W.1 _) = 0
    rw [hT0, map_zero]
  -- the degree-one element `s` with `ψ s = 1`
  obtain ⟨l, hl⟩ := (lSectionPiece_genSections_sLinear_bijective L U₂ e₂ W hW).2 1
  have hl' : ψ (symGradedAlgebra.genSections _ W.1 (sLinear L W.1 l)) = 1 := hl
  -- `q` is in the image of `fromOfGlobalSections ψ`
  have hmem := AlgebraicGeometry.Proj.mem_range_fromOfGlobalSections_of_forall_mem_span _ ψ
    (localRingHom_map_irrelevant _ (CategoryTheory.CategoryStruct.id X) _ (lSection.quotientMap L) U₂ e₂ W W.1 W.2
      (lSectionPiece_le U₂ W hW))
    (symGradedAlgebra.genSections_mem_sectionsGrading _ W.1 (oFunctional L ε W.1))
    (symGradedAlgebra.genSections_mem_sectionsGrading _ W.1 (sLinear L W.1 l))
    (hl' ▸ isUnit_one)
    (fun r => by
      obtain ⟨r', hr'⟩ := (lSectionPiece_sectionsUnitHom_bijective L U₂ e₂ W hW).2 r
      refine ⟨(symGradedAlgebra (dual _)).sectionsUnitHom W.1 r', ?_, hr'⟩
      rw [← symGradedAlgebra.symLiftHom_algebraMap]
      exact symGradedAlgebra.symLiftHom_mem_sectionsGrading _ W.1
        (MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetric_algebraMap_mem _ _ r'))
    (fun k a ha h => lSectionPiece_kernel L U₂ e₂ W ε hW k a ha hT0' h) q hq
  obtain ⟨y, hy⟩ := hmem
  refine ⟨W.1.ι.base y, ?_⟩
  have hres := lift_restrict _ (CategoryTheory.CategoryStruct.id X) _ (lSection.quotientMap L) U₂ e₂ W W.1 W.2
    (lSectionPiece_le U₂ W hW)
  change (W.1.ι ≫ lSection L).base y = _
  unfold AlgebraicGeometry.Scheme.lSection
  rw [hres]
  unfold liftLocal
  change ((relativeProj.affineIso _ W).inv ≫ ((relativeProj _).hom ⁻¹ᵁ W.1).ι).base
    ((AlgebraicGeometry.Proj.fromOfGlobalSections _ ψ _).base y) = _
  rw [hy]

end Main

end AlgebraicGeometry.Scheme.totalSpace

end
