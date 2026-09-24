import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.ConstantSheaf.Stacks0a38ConstantInclusion
import MiyaokaMori.AlgebraicGeometry.Cohomology.ConstantSheaf.ExtendByZeroConstantUnitSection

/-! # The canonical inclusion `j_!ℤ_U ⟶ ℤ_X` on the unit section

`constantInclusion U : j_!ℤ_U ⟶ ℤ_X` (`Stacks0a38ConstantInclusion.lean`) is "the section `1` of `ℤ_X` over `U`".
This file makes that computable:
* `constantInclusion_unitSection`: `c_U` sends the unit section `e_U ∈ (j_!ℤ_U)(U)` to the constant section
  `1 ∈ ℤ_X(U)`. Since `c_U = extendByZeroDesc U ι` with `ι = (restrictConstantSheafIso U ℤ).inv : ℤ_U ≅ (ℤ_X)|_U` an
  *abstract* mate isomorphism (built from Mathlib's `Adjunction.ofIsRightAdjoint`), this needs a computation:
  the unit of `restrictPushforwardAdjunction U` is the restriction map (`restrictPushforwardAdjunction_unit_app`;
  the abstract choice cancels by `Adjunction.unit_leftAdjointUniq_hom_app`, and the Kan-extension unit of
  Mathlib's concrete pullback is computed on sections), and the mate iso is compatible with the units
  (`unit_natIsoOfRightAdjointNatIso_hom_app`), whence `ι_W(1) = 1` (`restrictConstantSheafIso_inv_app_constSec`);
* consequences: `constantInclusion_eq_sectionDesc` (`c_U = sectionDesc ℤ_X U 1`),
  `constantInclusion_extendConstSec` (`c_U` sends the constant section `z` over `V ⊆ U` to `z ∈ ℤ_X(V)`),
  `restrictExtend_comp_constantInclusion` (`ρ_{W,U} ≫ c_U = c_W`), `zsmul_constantInclusion_unitSection`
  (`(n • c_V)_V(e_V) = n ∈ ℤ_X(V)`).

Source: Stacks 0A38 (the sections `n_i ∈ ℤ_X(V_i)`); Stacks 00A5. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

noncomputable section

namespace TopCat.Sheaf

/-- The unit of Mathlib's Kan-extension pullback adjunction
`Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` (`(Lan ⊣ whiskeringLeft).comp
(sheafification)`, restricted along `sheafToPresheaf`), on the underlying presheaves: the Kan-extension unit
`lanUnit` followed by `toSheafify` (`Adjunction.map_restrictFullyFaithful_unit_app`, `Adjunction.comp_unit_app`,
`Functor.lanAdjunction_unit`, `sheafificationAdjunction_unit_app`). -/
theorem sheafPullbackConstruction_unit_app_hom {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) (A : Type u₃) [Category.{v₃} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsContinuous J K] [HasWeakSheafify K A] [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F]
    (F : CategoryTheory.Sheaf J A) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G A J K).unit.app F).hom =
      G.op.lanUnit.app F.obj ≫ Functor.whiskerLeft G.op (toSheafify K (G.op.lan.obj F.obj)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (((G.op.lanAdjunction A).comp (sheafificationAdjunction K A)))
    (fullyFaithfulSheafToPresheaf J A) (Functor.FullyFaithful.id _)
    (L := Functor.sheafPullbackConstruction.sheafPullback G A J K) (R := G.sheafPushforwardContinuous A J K)
    (Iso.refl _) (Iso.refl _) F
  refine Eq.trans h ?_
  simp only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit, sheafificationAdjunction_unit_app,
    Iso.refl_hom, NatTrans.id_app, Functor.comp_obj, Functor.whiskeringLeft_obj_map]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

/-- `toSheafify P ≫ (sheafify(φ) ≫ (sheafify Q ≅ Q)) = φ` for a presheaf map `φ : P ⟶ Q` into a sheaf `Q`
(the identification `sheafify Q ≅ Q` is `isoSheafify`, transported to the sheaf category by `preimageIso`). -/
theorem toSheafify_comp_presheafToSheaf_map_preimageIso_hom {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) {D : Type u₂} [Category.{v₂} D] [HasWeakSheafify J D]
    {P Q : Cᵒᵖ ⥤ D} (φ : P ⟶ Q) (hQ : CategoryTheory.Presheaf.IsSheaf J Q) :
    toSheafify J P ≫ ((presheafToSheaf J D).map φ ≫
      ((fullyFaithfulSheafToPresheaf J D).preimageIso (X := (presheafToSheaf J D).obj Q) (Y := ⟨Q, hQ⟩)
        (isoSheafify J hQ).symm).hom).hom = φ := by
  simp [isoSheafify_inv]

/-- For an open map `f` and a presheaf `P` on the target, the Kan-extension unit `P(V) ⟶ (Lan P)(f⁻¹V)` followed by
Mathlib's identification `(Lan P)(f⁻¹V) ≅ P(f(f⁻¹V))` (`IsOpenMap.pullbackObjIso`, the colimit over the
costructured arrows `{V' : f⁻¹V ≤ f⁻¹V'}`, which has the terminal object `V' = f(f⁻¹V)`) is the restriction map
`P(V) ⟶ P(f(f⁻¹V))` (`IsColimit.comp_coconePointUniqueUpToIso_hom`, `coconeOfDiagramTerminal`). -/
theorem lanUnit_app_app_comp_pullbackObjIso_hom_app {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
    (P : Y.Presheaf AddCommGrpCat.{u}) (V : Opens Y) :
    ((Opens.map f).op.lanUnit.app P).app (op V) ≫
        (hf.pullbackObjIso P).hom.app (op ((Opens.map f).obj V)) =
      P.map (homOfLE (show hf.functor.obj ((Opens.map f).obj V) ≤ V from
        fun x hx => by obtain ⟨y, hy, rfl⟩ := hx; exact hy)).op := by
  have e1 : ((Opens.map f).op.lanUnit.app P).app (op V) =
      ((Functor.LeftExtension.mk _ ((Opens.map f).op.leftKanExtensionUnit P)).coconeAt
        (op ((Opens.map f).obj V))).ι.app (CostructuredArrow.mk (𝟙 _)) := by
    show _ = ((Opens.map f).op.leftKanExtensionUnit P).app (op V) ≫
      ((Opens.map f).op.leftKanExtension P).map (𝟙 _)
    rw [CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
    rfl
  rw [e1, IsOpenMap.pullbackObjIso_hom_app]
  unfold TopCat.Presheaf.pullbackObjObjOfImageOpen
  dsimp only
  refine Eq.trans (IsColimit.comp_coconePointUniqueUpToIso_hom
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit P (op ((Opens.map f).obj V)))
    (colimitOfDiagramTerminal _ _) (CostructuredArrow.mk (𝟙 _))) ?_
  dsimp [colimitOfDiagramTerminal, coconeOfDiagramTerminal]
  exact congrArg P.map (Subsingleton.elim _ _)

/-- the same for the natural isomorphism `IsOpenMap.pullbackIso` -/
theorem lanUnit_app_app_comp_pullbackIso_hom_app_app {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)
    (P : Y.Presheaf AddCommGrpCat.{u}) (V : Opens Y) :
    ((Opens.map f).op.lanUnit.app P).app (op V) ≫
        (hf.pullbackIso.hom.app P).app (op ((Opens.map f).obj V)) =
      P.map (homOfLE (show hf.functor.obj ((Opens.map f).obj V) ≤ V from
        fun x hx => by obtain ⟨y, hy, rfl⟩ := hx; exact hy)).op := by
  unfold IsOpenMap.pullbackIso
  simp only [NatIso.ofComponents_hom_app]
  exact lanUnit_app_app_comp_pullbackObjIso_hom_app hf P V


variable {X : TopCat.{u}} (U : Opens X)

/-- **The unit of `restrictPushforwardAdjunction` is the restriction map**, on sections: for `F` a sheaf on `X`
and `V` open, `η_V : F(V) ⟶ F(j(j⁻¹V)) = F(V ⊓ U)` is `F.map (V ⊓ U ≤ V)`. Proof: `restrictPushforwardAdjunction U
= pp.ofNatIsoLeft sheafPullbackIso` with `pp = TopCat.Sheaf.pullbackPushforwardAdjunction` (abstract,
`Adjunction.ofIsRightAdjoint`) and `sheafPullbackIso = leftAdjointUniq pp pp' ≪≫ e` (`pp'` the Kan-extension
adjunction); by `Adjunction.ofNatIsoLeft_unit` and `Adjunction.unit_leftAdjointUniq_hom_app` the abstract choice
cancels, `η = pp'.unit ≫ j_*(e)`, and the three lemmas above compute this composite. Stated for
`F : TopCat.Sheaf` so that `rw`/`simp` see the category instances used by Mathlib's constructions. -/
theorem restrictPushforwardAdjunction_unit_app_apply
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : (Opens X)ᵒᵖ) (s : F.presheaf.obj V) :
    (((restrictPushforwardAdjunction U).unit.app F).hom.app V).hom s =
      (F.presheaf.map (homOfLE (functor_map_le U V.unop)).op).hom s := by
  have h : (restrictPushforwardAdjunction U).unit =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (Opens.inclusion' U)).unit ≫
        Functor.whiskerRight ((Opens.isOpenEmbedding U).sheafPullbackIso AddCommGrpCat.{u}).hom
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)) :=
    Adjunction.ofNatIsoLeft_unit _ _
  rw [h, NatTrans.comp_app, Functor.whiskerRight_app]
  unfold IsOpenEmbedding.sheafPullbackIso
  simp only [Iso.trans_hom, NatTrans.comp_app, NatIso.ofComponents_hom_app]
  rw [Functor.map_comp, ← Category.assoc]
  unfold TopCat.Sheaf.pullbackIso Functor.sheafPullbackConstruction.sheafPullbackIso
    TopCat.Sheaf.pullbackPushforwardAdjunction
  erw [Adjunction.unit_leftAdjointUniq_hom_app]
  erw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  erw [TopCat.Sheaf.pushforward_map, TopCat.Presheaf.pushforward_map_app']
  erw [sheafPullbackConstruction_unit_app_hom]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app]
  erw [Category.assoc]
  erw [← NatTrans.comp_app]
  erw [Iso.trans_hom, Functor.mapIso_hom, toSheafify_comp_presheafToSheaf_map_preimageIso_hom]
  erw [lanUnit_app_app_comp_pullbackIso_hom_app_app]
  rfl

/-- the unit of `restrictPushforwardAdjunction U` at `F` is `restrictUnit U F` (`Stacks02uxExtendByZeroDesc.lean`) -/
theorem restrictPushforwardAdjunction_unit_app
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (restrictPushforwardAdjunction U).unit.app F = restrictUnit U F := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  ext s
  exact restrictPushforwardAdjunction_unit_app_apply U F V s


section Mate

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {F F' : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (r : G ≅ G')

set_option linter.deprecated false in
/-- components of the mate iso `Adjunction.natIsoOfRightAdjointNatIso` (deprecated in Mathlib in favour of
`conjugateIsoEquiv`, but it is what `restrictConstantSheafNatIso` uses): `Φ.hom.app A` is the transpose of
`adj2.unit.app A` along `adj1.ofNatIsoRight r` (unfold `NatIso.removeOp`, `FullyFaithful.isoEquiv`,
`Coyoneda.fullyFaithful.preimage f = (f.app _ (𝟙 _)).op`) -/
theorem natIsoOfRightAdjointNatIso_hom_app (A : C) :
    (Adjunction.natIsoOfRightAdjointNatIso adj1 adj2 r).hom.app A =
      ((adj1.ofNatIsoRight r).homEquiv A (F'.obj A)).symm (adj2.unit.app A) := by
  change ((Adjunction.leftAdjointsCoyonedaEquiv adj2 (adj1.ofNatIsoRight r)).hom.app (op A)).app (F'.obj A)
    (𝟙 _) = _
  simp [Adjunction.leftAdjointsCoyonedaEquiv, Adjunction.homEquiv_id]

set_option linter.deprecated false in
/-- unit compatibility of the mate iso: `unit₁ ≫ G(Φ) ≫ r = unit₂` -/
theorem unit_natIsoOfRightAdjointNatIso_hom_app (A : C) :
    adj1.unit.app A ≫ G.map ((Adjunction.natIsoOfRightAdjointNatIso adj1 adj2 r).hom.app A) ≫
      r.hom.app (F'.obj A) = adj2.unit.app A := by
  have h := ((adj1.ofNatIsoRight r).homEquiv A (F'.obj A)).apply_symm_apply (adj2.unit.app A)
  rw [Adjunction.homEquiv_unit] at h
  rw [natIsoOfRightAdjointNatIso_hom_app]
  conv_rhs => rw [← h]
  simp [Adjunction.ofNatIsoRight]

end Mate

/-- the unit of the constant-sheaf adjunction is `toSheafify` at the terminal object -/
theorem constantSheafAdj_unit_app_eq {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    (D : Type u₂) [Category.{v₂} D] [HasWeakSheafify J D] {T : C} (hT : IsTerminal T) (A : D) :
    (constantSheafAdj J D hT).unit.app A = (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op T) := by
  simp [constantSheafAdj, Adjunction.comp_unit_app]
  rfl

variable {X : TopCat.{u}} (U : Opens X)

/-- The mate isomorphism `Φ = restrictConstantSheafNatIso U : (ℤ_X)|_U ≅ ℤ_U` (`Stacks02uzExtendByZero.lean`),
at `ℤ` and over `j⁻¹⊤`, sends the constant section `1 ∈ ℤ_X(j(j⁻¹⊤))` to the constant section `1 ∈ ℤ_U(j⁻¹⊤)`
(`= ℤ_U(⊤)`). Proof: unit compatibility of the mate iso (`unit_natIsoOfRightAdjointNatIso_hom_app`) with
`adjA = (constantSheafAdj X).comp (restrictPushforwardAdjunction U)`, `adjB = constantSheafAdj U`; the units are
`toSheafify` at `⊤` (`constantSheafAdj_unit_app_eq`) and the restriction map (`restrictPushforwardAdjunction_unit_app`),
and `constSec_res`. -/
theorem restrictConstantSheafNatIso_hom_app_constSec :
    ((((restrictConstantSheafNatIso U).hom.app (AddCommGrpCat.of (ULift.{u} ℤ))).hom.app
        (op ((Opens.map (Opens.inclusion' U)).obj ⊤))).hom
      (constSec ((Opens.isOpenEmbedding U).functor.obj ((Opens.map (Opens.inclusion' U)).obj ⊤)) 1) : (constZ U).obj.obj (op ((Opens.map (Opens.inclusion' U)).obj ⊤))) =
    constSec ((Opens.map (Opens.inclusion' U)).obj ⊤) 1 := by
  have h := unit_natIsoOfRightAdjointNatIso_hom_app
    ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).comp
      (restrictPushforwardAdjunction U))
    (constantSheafAdj (Opens.grothendieckTopology U) AddCommGrpCat.{u} isTerminalTop)
    (Iso.refl _) (AddCommGrpCat.of (ULift.{u} ℤ))
  have h1 := congrArg (fun m => m.hom (⟨1⟩ : ULift.{u} ℤ)) h
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at h1
  erw [Adjunction.comp_unit_app] at h1
  rw [restrictPushforwardAdjunction_unit_app] at h1
  erw [constantSheafAdj_unit_app_eq, constantSheafAdj_unit_app_eq] at h1
  have h2 := constSec_res (T := X) (functor_map_le U ⊤) 1
  rw [← h2]
  exact h1

/-- `ι = (restrictConstantSheafIso U ℤ).inv : ℤ_U ⟶ (ℤ_X)|_U` sends the constant section `1` over `j⁻¹⊤` to the
constant section `1` over `j(j⁻¹⊤)` (invert the previous lemma with `Iso.hom_inv_id`) -/
theorem restrictConstantSheafIso_inv_app_constSec_top :
    ((restrictConstantSheafIso U (AddCommGrpCat.of (ULift.{u} ℤ))).inv.hom.app
        (op ((Opens.map (Opens.inclusion' U)).obj ⊤))).hom
      (constSec ((Opens.map (Opens.inclusion' U)).obj ⊤) 1) =
    constSec ((Opens.isOpenEmbedding U).functor.obj ((Opens.map (Opens.inclusion' U)).obj ⊤)) 1 := by
  rw [← restrictConstantSheafNatIso_hom_app_constSec]
  have h := congrArg (fun m => (m.hom.app (op ((Opens.map (Opens.inclusion' U)).obj ⊤))).hom
      (constSec ((Opens.isOpenEmbedding U).functor.obj ((Opens.map (Opens.inclusion' U)).obj ⊤)) 1))
    (Iso.hom_inv_id (restrictConstantSheafIso U (AddCommGrpCat.of (ULift.{u} ℤ))))
  exact h

/-- `ι` sends the constant section `1` over any open `W ⊆ U` to the constant section `1` over `j(W)` (naturality
of `ι` and `constSec_res`, from the case `W = j⁻¹⊤`) -/
theorem restrictConstantSheafIso_inv_app_constSec (W : Opens U) :
    ((restrictConstantSheafIso U (AddCommGrpCat.of (ULift.{u} ℤ))).inv.hom.app (op W)).hom (constSec W 1) =
    constSec ((Opens.isOpenEmbedding U).functor.obj W) 1 := by
  have hW : W ≤ (Opens.map (Opens.inclusion' U)).obj ⊤ := le_top
  rw [← constSec_res hW 1]
  have hnat := congrArg (fun g => g.hom (constSec ((Opens.map (Opens.inclusion' U)).obj ⊤) 1))
    ((restrictConstantSheafIso U (AddCommGrpCat.of (ULift.{u} ℤ))).inv.hom.naturality (homOfLE hW).op)
  refine Eq.trans hnat ?_
  change ((TopCat.Sheaf.restrict (constZ X) U).obj.map (homOfLE hW).op).hom
    (((restrictConstantSheafIso U (AddCommGrpCat.of (ULift.{u} ℤ))).inv.hom.app
      (op ((Opens.map (Opens.inclusion' U)).obj ⊤))).hom
        (constSec ((Opens.map (Opens.inclusion' U)).obj ⊤) 1)) = _
  rw [restrictConstantSheafIso_inv_app_constSec_top]
  exact constSec_res (T := X)
    (V := (Opens.isOpenEmbedding U).functor.obj ((Opens.map (Opens.inclusion' U)).obj ⊤))
    (W := (Opens.isOpenEmbedding U).functor.obj W) (Set.image_mono hW) 1


/-- **The canonical inclusion on the unit section.** The canonical inclusion `c_U = constantInclusion U :
j_!ℤ_U ⟶ ℤ_X` sends the unit section `e_U ∈ (j_!ℤ_U)(U)` (`unitSection U`, the image of `1`) to the constant
section `1 ∈ ℤ_X(U)` (`constSec U 1`, the image of `1` under `toSheafify`).

**Proof.** `constantInclusion U = extendByZeroDesc U ι` with `ι = (restrictConstantSheafIso U ℤ).inv : ℤ_U ⟶ (ℤ_X)|_U`.
Unwinding `extendByZeroDesc_val_app_toSheafify` and `extendByZeroDescApp_of_le`, `c_U(e_U)` is the restriction
to `U` of `ι_{j⁻¹U}(1) ∈ ℤ_X(j(j⁻¹U))`, which is the constant section `1` by
`restrictConstantSheafIso_inv_app_constSec` (the value of the mate isomorphism on the constant sections; see the
lemmas above), and `constSec_res` finishes.

Source: Stacks 0A38 (cohomology-lemma-subsheaf-of-constant-sheaf), proof, paragraph 1 ("the sections
`n_i ∈ ℤ_X(U_i)`"); Stacks 00A5 (`j_! ⊣ j^{-1}`). -/
theorem constantInclusion_unitSection :
    ((constantInclusion U).hom.app (op U)).hom (unitSection U) = constSec U 1 := by
  unfold constantInclusion unitSection
  rw [extendByZeroDesc_val_app_toSheafify, extendByZeroDescApp_of_le U _ (op U) le_rfl]
  erw [restrictConstantSheafIso_inv_app_constSec]
  exact constSec_res _ 1

/-- `c_U` is the morphism corresponding to the section `1 ∈ ℤ_X(U)` -/
theorem constantInclusion_eq_sectionDesc :
    constantInclusion U = sectionDesc (constZ X) U (constSec U 1) :=
  hom_ext_of_unitSection U (by rw [constantInclusion_unitSection, sectionDesc_unitSection])

/-- `c_U` sends the constant section `z` over `V ⊆ U` to the constant section `z ∈ ℤ_X(V)` -/
theorem constantInclusion_extendConstSec {V : Opens X} (hV : V ≤ U) (z : ℤ) :
    ((constantInclusion U).hom.app (op V)).hom (extendConstSec U hV z) = constSec V z := by
  rw [constantInclusion_eq_sectionDesc, sectionDesc_extendConstSec, constSec_res, zsmul_constSec_one]

/-- **compatibility of the canonical inclusions**: `ρ_{W,U} ≫ c_U = c_W` for `W ≤ U` -/
theorem restrictExtend_comp_constantInclusion {W : Opens X} (h : W ≤ U) :
    restrictExtend U h ≫ constantInclusion U = constantInclusion W := by
  apply hom_ext_of_unitSection
  change ((constantInclusion U).hom.app (op W)).hom (((restrictExtend U h).hom.app (op W)).hom (unitSection W)) = _
  rw [restrictExtend_unitSection, unitSection_eq, extendConstSec_res, constantInclusion_extendConstSec,
    constantInclusion_unitSection]

/-- `(n • c_V)_V (e_V) = n ∈ ℤ_X(V)` -/
theorem zsmul_constantInclusion_unitSection (V : Opens X) (z : ℤ) :
    ((z • constantInclusion V).hom.app (op V)).hom (unitSection V) = constSec V z := by
  change z • ((constantInclusion V).hom.app (op V)).hom (unitSection V) = _
  rw [constantInclusion_unitSection, zsmul_constSec_one]

end TopCat.Sheaf

end
