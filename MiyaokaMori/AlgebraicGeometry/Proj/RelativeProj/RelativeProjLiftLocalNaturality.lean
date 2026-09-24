import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftData
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion

/-! # Naturality of the local ring map of a lift into a relative Proj

Three compatibilities of the general-form local ring homomorphism
`relativeProj.liftLocalRingHomAux D ι e' W hW : A(W) →+* Γ(Y, O)` (`RelativeProjLiftData.lean`), the
ingredients of `liftLocal_compat`:

* **composition along `j : Y' → Y`** (`liftLocalRingHomAux_comp`): `j^♯ ∘ Aux(ι, e', W) = Aux(j ≫ ι, e'_j, W)`,
  where `e'_j := trivComp j ι e'` is the trivialization obtained by pulling `e'` back along `j` and rearranging
  with `pullbackComp` and `pullbackUnitIso`;
* **change of `W`** (`liftLocalRingHomAux_restrict`): for `W' ≤ W`, `Aux(ι, e', W) = Aux(ι, e', W') ∘ res_{W'←W}`;
* **change of trivialization** (`liftLocalRingHomAux_unit_scale`): two trivializations `e₁', e₂'` differ by the
  automorphism `a = e₁'⁻¹ ≫ e₂'` of `O_Y`, i.e. by multiplication with the global unit `u := a(1)`, so on a
  homogeneous element of degree `d`, `Aux(e₂') x = u^d · Aux(e₁') x`.

Source: Stacks 01O4 ("up to strict equivalence": a change of trivialization is a graded rescaling by a global
unit), 01N8. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.Functor.OplaxMonoidal
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/-! ## Compatibility of the tensor-power comparison maps with composition -/

/-- Compatibility of `pullbackComp.inv` with the comparison map `δ` (inverse version, with a tail `h`):
`C⁻¹_{A⊗B} ≫ j^*δ_g ≫ δ_j ≫ (a ⊗ a') ≫ h = δ_{j≫g} ≫ ((C⁻¹_A ≫ a) ⊗ (C⁻¹_B ≫ a')) ≫ h`. -/
theorem pullbackComp_inv_app_δ_comp (j : X ⟶ Y) (g : Y ⟶ Z) (A B : Z.Modules)
    {A' B' E : X.Modules}
    (a : (pullback j).obj ((pullback g).obj A) ⟶ A')
    (a' : (pullback j).obj ((pullback g).obj B) ⟶ B') (h : A' ⊗ B' ⟶ E) :
    (pullbackComp j g).inv.app (A ⊗ B) ≫ (pullback j).map (pullbackTensorObjHom g A B) ≫
        pullbackTensorObjHom j _ _ ≫ (a ⊗ₘ a') ≫ h =
      pullbackTensorObjHom (j ≫ g) A B ≫
        (((pullbackComp j g).inv.app A ≫ a) ⊗ₘ ((pullbackComp j g).inv.app B ≫ a')) ≫ h := by
  have hD := pullbackComp_hom_app_pullbackTensorObjHom j g A B
  have hs : (a ⊗ₘ a') =
      ((pullbackComp j g).hom.app A ⊗ₘ (pullbackComp j g).hom.app B) ≫
      (((pullbackComp j g).inv.app A ≫ a) ⊗ₘ ((pullbackComp j g).inv.app B ≫ a')) := by
    rw [tensorHom_comp_tensorHom, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  rw [hs]
  simp only [Category.assoc]
  rw [← reassoc_of% hD, Iso.inv_hom_id_app_assoc]

/-- (a) `pullbackMonoidalPow` along a composite:
`C⁻¹_{M^{⊗m}} ≫ j^*(P_g M m) ≫ P_j (g^*M) m = P_{j≫g} M m ≫ (C⁻¹_M)^{⊗m}`. -/
@[reassoc]
theorem pullbackMonoidalPow_comp (j : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) : ∀ m : ℕ,
    (pullbackComp j g).inv.app (monoidalPow M m) ≫ (pullback j).map (pullbackMonoidalPow g M m) ≫
        pullbackMonoidalPow j ((pullback g).obj M) m =
      pullbackMonoidalPow (j ≫ g) M m ≫ monoidalPowMap ((pullbackComp j g).inv.app M) m
  | 0 => by
    show (pullbackComp j g).inv.app (𝟙_ Z.Modules) ≫ (pullback j).map (pullbackUnitIso g).hom ≫
        (pullbackUnitIso j).hom = (pullbackUnitIso (j ≫ g)).hom ≫ 𝟙 _
    rw [Category.comp_id, ← pullbackComp_hom_app_pullbackUnitIso_hom]
    erw [Iso.inv_hom_id_app_assoc]
  | m + 1 => by
    show (pullbackComp j g).inv.app (monoidalPow M m ⊗ M) ≫
        (pullback j).map (pullbackTensorObjHom g (monoidalPow M m) M ≫
          pullbackMonoidalPow g M m ▷ (pullback g).obj M) ≫
        (pullbackTensorObjHom j _ _ ≫
          pullbackMonoidalPow j ((pullback g).obj M) m ▷ (pullback j).obj ((pullback g).obj M)) =
      (pullbackTensorObjHom (j ≫ g) (monoidalPow M m) M ≫
          pullbackMonoidalPow (j ≫ g) M m ▷ (pullback (j ≫ g)).obj M) ≫
        (monoidalPowMap ((pullbackComp j g).inv.app M) m ⊗ₘ (pullbackComp j g).inv.app M)
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    have hnat : (pullback j).map (pullbackMonoidalPow g M m ▷ (pullback g).obj M) ≫
        pullbackTensorObjHom j (monoidalPow ((pullback g).obj M) m) ((pullback g).obj M) =
        pullbackTensorObjHom j _ _ ≫
          (pullback j).map (pullbackMonoidalPow g M m) ▷ (pullback j).obj ((pullback g).obj M) :=
      (δ_natural_left (pullback j) (pullbackMonoidalPow g M m) ((pullback g).obj M)).symm
    rw [reassoc_of% hnat, ← comp_whiskerRight, ← tensorHom_id, ← tensorHom_id]
    have key := pullbackComp_inv_app_δ_comp j g (monoidalPow M m) M
      ((pullback j).map (pullbackMonoidalPow g M m) ≫ pullbackMonoidalPow j ((pullback g).obj M) m)
      (𝟙 _) (𝟙 _)
    simp only [Category.comp_id] at key
    rw [key, pullbackMonoidalPow_comp j g M m, tensorHom_comp_tensorHom]
    erw [Category.comp_id]

/-- (b) `pullbackMonoidalPow` is natural in module maps: `j^*(φ^{⊗m}) ≫ P_j W m = P_j V m ≫ (j^*φ)^{⊗m}`. -/
@[reassoc]
theorem pullbackMonoidalPow_naturality (j : X ⟶ Y) {V W : Y.Modules} (φ : V ⟶ W) : ∀ m : ℕ,
    (pullback j).map (monoidalPowMap φ m) ≫ pullbackMonoidalPow j W m =
      pullbackMonoidalPow j V m ≫ monoidalPowMap ((pullback j).map φ) m
  | 0 => by
    show (pullback j).map (𝟙 _) ≫ (pullbackUnitIso j).hom = (pullbackUnitIso j).hom ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | m + 1 => by
    show (pullback j).map (monoidalPowMap φ m ⊗ₘ φ) ≫
        (pullbackTensorObjHom j (monoidalPow W m) W ≫ pullbackMonoidalPow j W m ▷ (pullback j).obj W) =
      (pullbackTensorObjHom j (monoidalPow V m) V ≫ pullbackMonoidalPow j V m ▷ (pullback j).obj V) ≫
        (monoidalPowMap ((pullback j).map φ) m ⊗ₘ (pullback j).map φ)
    rw [pullbackTensorObjHom_eq_δ, pullbackTensorObjHom_eq_δ, ← δ_natural_assoc,
      ← tensorHom_id, ← tensorHom_id]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
      pullbackMonoidalPow_naturality j φ m]

/-- Two endomorphisms of the unit object, tensored and followed by the left unitor: `(p ⊗ q) ≫ λ = λ ≫ p ≫ q`. -/
theorem tensorHom_leftUnitor_unit {C : Type*} [Category C] [MonoidalCategory C]
    (p q : 𝟙_ C ⟶ 𝟙_ C) :
    (p ⊗ₘ q) ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ p ≫ q := by
  rw [tensorHom_def, Category.assoc, leftUnitor_naturality, unitors_equal,
    ← Category.assoc, rightUnitor_naturality, Category.assoc]

/-- (c) `unitPowCollapse` along pullback: `j^*(collapse_Y m) ≫ U_j = P_j 𝟙 m ≫ (U_j)^{⊗m} ≫ collapse_X m`. -/
theorem pullback_map_unitPowCollapse (j : X ⟶ Y) : ∀ m : ℕ,
    (pullback j).map (unitPowCollapse Y m) ≫ (pullbackUnitIso j).hom =
      pullbackMonoidalPow j (𝟙_ Y.Modules) m ≫ monoidalPowMap (pullbackUnitIso j).hom m ≫
        unitPowCollapse X m
  | 0 => by
    show (pullback j).map (𝟙 _) ≫ (pullbackUnitIso j).hom = (pullbackUnitIso j).hom ≫ 𝟙 _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.comp_id]
  | m + 1 => by
    show (pullback j).map ((unitPowCollapse Y m ▷ 𝟙_ Y.Modules) ≫ (λ_ (𝟙_ Y.Modules)).hom) ≫
        (pullbackUnitIso j).hom =
      (pullbackTensorObjHom j (monoidalPow (𝟙_ Y.Modules) m) (𝟙_ Y.Modules) ≫
          pullbackMonoidalPow j (𝟙_ Y.Modules) m ▷ (pullback j).obj (𝟙_ Y.Modules)) ≫
        (monoidalPowMap (pullbackUnitIso j).hom m ⊗ₘ (pullbackUnitIso j).hom) ≫
        ((unitPowCollapse X m ▷ 𝟙_ X.Modules) ≫ (λ_ (𝟙_ X.Modules)).hom)
    -- `j^*(λ_𝟙).hom ≫ U_j = δ ≫ (U_j ⊗ U_j) ≫ λ_𝟙`
    have hlam : (pullback j).map (λ_ (𝟙_ Y.Modules)).hom ≫ (pullbackUnitIso j).hom =
        pullbackTensorObjHom j (𝟙_ Y.Modules) (𝟙_ Y.Modules) ≫
          ((pullbackUnitIso j).hom ⊗ₘ (pullbackUnitIso j).hom) ≫ (λ_ (𝟙_ X.Modules)).hom := by
      rw [tensorHom_def]
      simp only [Category.assoc]
      erw [leftUnitor_naturality]
      rw [pullbackTensorObjHom_eq_δ, ← pullback_η, left_unitality_hom_assoc]
    rw [CategoryTheory.Functor.map_comp, Category.assoc, hlam, pullbackTensorObjHom_eq_δ, pullbackTensorObjHom_eq_δ,
      ← δ_natural_left_assoc, ← tensorHom_id]
    simp only [Category.assoc]
    erw [tensorHom_comp_tensorHom_assoc]
    erw [Category.id_comp]
    rw [pullback_map_unitPowCollapse j m, ← tensorHom_id, ← tensorHom_id]
    erw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
    simp only [Category.id_comp, Category.assoc]
    erw [Category.comp_id]

/-! ## Pullback of a trivialization along `j`; `liftLocalHomAux` along a composite -/

/-- The pullback of a trivialization `e' : ι^*M ≅ O_Y` along `j : Y' → Y`:
`(j ≫ ι)^*M ≅ j^*ι^*M ≅ j^*O_Y ≅ O_{Y'}`. (`relativeProj.liftLocalTriv` is the case `j = (V ↪ U)`, `ι = U.ι`.) -/
noncomputable def trivComp {T : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) (ι : Y ⟶ T) (M : T.Modules)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (pullback (j ≫ ι)).obj M ≅ SheafOfModules.unit X.ringCatSheaf :=
  ((pullbackComp j ι).app M).symm ≪≫ (pullback j).mapIso e' ≪≫ pullbackUnitIso j

theorem trivComp_hom {T : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) (ι : Y ⟶ T) (M : T.Modules)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (trivComp j ι M e').hom =
      (pullbackComp j ι).inv.app M ≫ (pullback j).map e'.hom ≫ (pullbackUnitIso j).hom := rfl

/-- The pseudofunctor associativity law on an object `A`:
`C⁻¹_{j, ι≫f}.app A ≫ j^*(C⁻¹_{ι,f}.app A) = C⁻¹_{j≫ι, f}.app A ≫ C⁻¹_{j,ι}.app (f^*A)`
(Mathlib `pseudofunctor_associativity`; `(j ≫ ι) ≫ f` and `j ≫ ι ≫ f` are definitionally equal). -/
theorem pullbackComp_inv_app_assoc {T : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) (ι : Y ⟶ Z)
    (f : Z ⟶ T) (A : T.Modules) :
    (pullbackComp j (ι ≫ f)).inv.app A ≫ (pullback j).map ((pullbackComp ι f).inv.app A) =
      (pullbackComp (j ≫ ι) f).inv.app A ≫ (pullbackComp j ι).inv.app ((pullback f).obj A) := by
  have h := NatTrans.congr_app (pseudofunctor_associativity j ι f) A
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at h
  erw [eqToHom_refl] at h
  set a := (pullbackComp j (ι ≫ f)).inv.app A
  set b := (pullback j).map ((pullbackComp ι f).inv.app A)
  set c := (pullbackComp j ι).hom.app ((pullback f).obj A)
  set d := (pullbackComp (j ≫ ι) f).hom.app A
  set c' := (pullbackComp j ι).inv.app ((pullback f).obj A)
  set d' := (pullbackComp (j ≫ ι) f).inv.app A
  have hcd : (c ≫ d) ≫ (d' ≫ c') = 𝟙 _ := by
    simp only [c, d, c', d', Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  have h2 : (a ≫ b) ≫ (c ≫ d) = 𝟙 _ := by simpa only [Category.assoc] using h
  calc a ≫ b = (a ≫ b) ≫ (c ≫ d) ≫ (d' ≫ c') := by rw [hcd]; erw [Category.comp_id]
    _ = d' ≫ c' := by
        rw [← Category.assoc (a ≫ b) (c ≫ d) (d' ≫ c'), h2]
        erw [Category.id_comp]

/-- `pullbackComp_inv_app_assoc` with a tail. -/
theorem pullbackComp_inv_app_assoc' {T : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) (ι : Y ⟶ Z)
    (f : Z ⟶ T) (A : T.Modules) {E : X.Modules}
    (h : (pullback j).obj ((pullback ι).obj ((pullback f).obj A)) ⟶ E) :
    (pullbackComp j (ι ≫ f)).inv.app A ≫ (pullback j).map ((pullbackComp ι f).inv.app A) ≫ h =
      (pullbackComp (j ≫ ι) f).inv.app A ≫ (pullbackComp j ι).inv.app ((pullback f).obj A) ≫ h := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ h) (pullbackComp_inv_app_assoc j ι f A)).trans (Category.assoc _ _ _))

/-- **`liftLocalHomAux` along a composite `j : Y' → Y`**:
`Φ^{j≫ι, e'_j}_m = C⁻¹_{j, ι≫f} ≫ j^*Φ^{ι,e'}_m ≫ U_j`. -/
theorem _root_.AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_comp
    {T W₀ : AlgebraicGeometry.Scheme.{u}} {S : W₀.GradedQCAlgebra} {f : T ⟶ W₀} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) (j : X ⟶ Y) (m : ℕ) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D (j ≫ ι) (trivComp j ι M e') m =
      (pullbackComp j (ι ≫ f)).inv.app (S.part m) ≫
        (pullback j).map (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m) ≫
        (pullbackUnitIso j).hom := by
  unfold AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [pullbackComp_inv_app_assoc' j ι f (S.part m)]
  erw [← reassoc_of% ((pullbackComp j ι).inv.naturality (D.Ψ m))]
  -- tail: C⁻¹_{M^m} ≫ j^*P_ι ≫ j^*(e'^{⊗m}) ≫ j^*coll ≫ U_j = P_{jι} ≫ (e'_j)^{⊗m} ≫ coll
  rw [pullback_map_unitPowCollapse j m]
  erw [pullbackMonoidalPow_naturality_assoc j e'.hom m]
  erw [pullbackMonoidalPow_comp_assoc j ι M m]
  rw [trivComp_hom, monoidalPowMap_comp, monoidalPowMap_comp]
  simp only [Category.assoc]

/-! ## On sections: `j^♯ ∘ Aux(ι, e', W) = Aux(j ≫ ι, e'_j, W)` -/

/-- `⊤ ≤ g⁻¹W ⟹ ⊤ ≤ (j ≫ g)⁻¹W`. -/
theorem top_le_comp_preimage_of_top_le {T : AlgebraicGeometry.Scheme.{u}} (j : X ⟶ Y) (g : Y ⟶ T) {W : T.Opens}
    (hW : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ W) : (⊤ : X.Opens) ≤ (j ≫ g) ⁻¹ᵁ W := by
  intro y _
  show g.base (j.base y) ∈ W
  exact hW (Set.mem_univ _)

/-- **`j^♯` expressed through `pullbackUnitIso` and the adjunction unit**: `j.app V z = U_j.app (j⁻¹V) (η_j z)`
(`homEquiv_pullbackUnitIso_hom_pbup` + `Adjunction.homEquiv_unit`). -/
theorem app_eq_pullbackUnitIso_app_unit (j : X ⟶ Y) (V : Y.Opens) (z : Γ(Y, V)) :
    j.app V z =
      (pullbackUnitIso j).hom.app (j ⁻¹ᵁ V)
        (((pullbackPushforwardAdjunction j).unit.app (SheafOfModules.unit Y.ringCatSheaf)).app V z) := by
  have h := homEquiv_pullbackUnitIso_hom_pbup j
  rw [Adjunction.homEquiv_unit] at h
  have h' := congrArg (fun k : SheafOfModules.unit Y.ringCatSheaf ⟶
    (pushforward j).obj (SheafOfModules.unit X.ringCatSheaf) => Hom.app k V z) h
  exact h'.symm

/-- A module-sheaf map commutes with restriction (the `Hom.app` form of `PresheafOfModules.naturality_apply`). -/
theorem hom_app_presheaf_map {P Q : Y.Modules} (φ : P ⟶ Q) {V V' : Y.Opens} (h : V' ≤ V) (a : Γ(P, V)) :
    φ.app V' (P.presheaf.map (homOfLE h).op a) = Q.presheaf.map (homOfLE h).op (φ.app V a) := by
  have := congr($(φ.mapPresheaf.naturality (homOfLE h).op) a)
  simpa using this

/-- The `app` of a scheme morphism commutes with restriction: `j^♯_⊤ (z|_⊤) = (j^♯_V z)|_⊤` (`⊤ ≤ V`). -/
theorem app_top_presheaf_map (j : X ⟶ Y) {V : Y.Opens} (hV : (⊤ : Y.Opens) ≤ V) (z : Γ(Y, V)) :
    j.app ⊤ (Y.presheaf.map (homOfLE hV).op z) =
      X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ j ⁻¹ᵁ V from
        fun y _ => hV (Set.mem_univ (j.base y)))).op (j.app V z) := by
  have := congr($(j.naturality (homOfLE hV).op) z)
  exact this

/-- **Compatibility with composition on sections**: `j^♯ (Aux(ι, e', W) m a) = Aux(j ≫ ι, e'_j, W) m a`. -/
theorem _root_.AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_comp
    {T W₀ : AlgebraicGeometry.Scheme.{u}} {S : W₀.GradedQCAlgebra} {f : T ⟶ W₀} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : W₀.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (j : X ⟶ Y) (m : ℕ)
    (a : S.sectionsPiece W m) :
    j.appTop (AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW m a) =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D (j ≫ ι) (trivComp j ι M e') W
        (top_le_comp_preimage_of_top_le j (ι ≫ f) hW) m a := by
  set g := ι ≫ f with hg
  set Φ := AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m with hΦ
  set Φ' := AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D (j ≫ ι) (trivComp j ι M e') m
    with hΦ'
  set η := (pullbackPushforwardAdjunction g).unit.app (S.part m) with hη
  set η' := (pullbackPushforwardAdjunction (j ≫ g)).unit.app (S.part m) with hη'
  change j.app ⊤ (Φ.app ⊤ (((pullback g).obj (S.part m)).presheaf.map (homOfLE hW).op (η.app W a))) =
    Φ'.app ⊤ (((pullback (j ≫ g)).obj (S.part m)).presheaf.map
      (homOfLE (top_le_comp_preimage_of_top_le j g hW)).op (η'.app W a))
  rw [hom_app_presheaf_map Φ hW]
  erw [hom_app_presheaf_map Φ' (top_le_comp_preimage_of_top_le j g hW)]
  erw [app_top_presheaf_map j hW]
  rw [app_eq_pullbackUnitIso_app_unit j (g ⁻¹ᵁ W)]
  rw [← unit_naturality_app j Φ (g ⁻¹ᵁ W)]
  rw [← pullbackComp_inv_app_unit j g (S.part m) W a]
  rw [hΦ', AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_comp]
  rfl

/-- **Compatibility with composition on ring homomorphisms**: `j^♯ ∘ Aux(ι, e', W) = Aux(j ≫ ι, e'_j, W)`. -/
theorem _root_.AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_comp
    {T W₀ : AlgebraicGeometry.Scheme.{u}} {S : W₀.GradedQCAlgebra} {f : T ⟶ W₀} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : W₀.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (j : X ⟶ Y) :
    j.appTop.hom.comp (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e' W hW) =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D (j ≫ ι) (trivComp j ι M e') W
        (top_le_comp_preimage_of_top_le j (ι ≫ f) hW) := by
  refine DirectSum.ringHom_ext fun m a => ?_
  change j.appTop (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e' W hW
      (DirectSum.of (S.sectionsPiece W) m a)) =
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D (j ≫ ι) (trivComp j ι M e') W
      (top_le_comp_preimage_of_top_le j (ι ≫ f) hW) (DirectSum.of (S.sectionsPiece W) m a)
  rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_of,
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_of]
  exact AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_comp D ι e' W hW j m a

/-! ## Change of `W`: `Aux(ι, e', W) = Aux(ι, e', W') ∘ res_{W'←W}` -/

/-- On sections: on the `m`-th piece, `Aux(W) a = Aux(W') (a|_{W'})` (the adjunction unit commutes with
restriction, `unit_app_map`). -/
theorem _root_.AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_restrict
    {T W₀ : AlgebraicGeometry.Scheme.{u}} {S : W₀.GradedQCAlgebra} {f : T ⟶ W₀} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    {W W' : W₀.Opens} (h : W' ≤ W) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W)
    (hW' : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W') (m : ℕ) (a : S.sectionsPiece W m) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW m a =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W' hW' m
        (S.sectionsRestrictPiece h m a) := by
  set g := ι ≫ f with hg
  set Φ := AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m with hΦ
  set η := (pullbackPushforwardAdjunction g).unit.app (S.part m) with hη
  change Φ.app ⊤ (((pullback g).obj (S.part m)).presheaf.map (homOfLE hW).op (η.app W a)) =
    Φ.app ⊤ (((pullback g).obj (S.part m)).presheaf.map (homOfLE hW').op
      (η.app W' ((S.part m).presheaf.map (homOfLE h).op a)))
  rw [unit_app_map g (S.part m) h a]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

/-- **Change of `W` on ring homomorphisms**: `Aux(ι, e', W) = Aux(ι, e', W') ∘ sectionsRestrict (W' ≤ W)`. -/
theorem _root_.AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_restrict
    {T W₀ : AlgebraicGeometry.Scheme.{u}} {S : W₀.GradedQCAlgebra} {f : T ⟶ W₀} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    {W W' : W₀.Opens} (h : W' ≤ W) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W)
    (hW' : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W') :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e' W hW =
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e' W' hW').comp
        (S.sectionsRestrict h).toRingHom := by
  refine DirectSum.ringHom_ext fun m a => ?_
  change AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e' W hW
      (DirectSum.of (S.sectionsPiece W) m a) =
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e' W' hW'
      (S.sectionsRestrictRingHom h (DirectSum.of (S.sectionsPiece W) m a))
  rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_of, S.sectionsRestrictRingHom_of h m a,
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_of]
  exact AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_restrict D ι e' h hW hW' m a

/-! ## Change of trivialization: rescaling by a unit -/

/-- The function `Γ(Y, O) → Γ(Y, O)` induced on global sections by an endomorphism `a` of the unit sheaf `O_Y`
(by definition `a.app ⊤`). -/
noncomputable def unitEndFun
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) (x : Γ(Y, ⊤)) :
    Γ(Y, ⊤) :=
  Hom.app a ⊤ x

/-- The global section `u := a(1)` corresponding to an endomorphism `a` of the unit sheaf `O_Y`. -/
noncomputable def unitEndSection
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) : Γ(Y, ⊤) :=
  unitEndFun a 1

theorem unitEndFun_comp
    (a b : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) (x : Γ(Y, ⊤)) :
    unitEndFun (a ≫ b) x = unitEndFun b (unitEndFun a x) := rfl

theorem unitEndFun_id (x : Γ(Y, ⊤)) : unitEndFun (𝟙 (SheafOfModules.unit Y.ringCatSheaf)) x = x := rfl

/-- An endomorphism of `O_Y` acts on global sections as multiplication by `u` (`O`-linearity + `1` generates). -/
theorem unitEndFun_eq_mul
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) (x : Γ(Y, ⊤)) :
    unitEndFun a x = x * unitEndSection a := by
  unfold unitEndFun unitEndSection
  have h1 : (x : Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤)) =
      x • ((1 : Γ(Y, ⊤)) : Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤)) :=
    ((smul_eq_mul x 1).trans (mul_one x)).symm
  conv_lhs => rw [h1]
  erw [Hom.app_smul]
  exact smul_eq_mul _ _

/-- The `m`-fold iterate `a ≫ ⋯ ≫ a` of `a`. -/
noncomputable def unitEndPow
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    ℕ → (SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf)
  | 0 => 𝟙 _
  | m + 1 => unitEndPow a m ≫ a

theorem unitEndFun_unitEndPow
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) (x : Γ(Y, ⊤)) :
    ∀ m : ℕ, unitEndFun (unitEndPow a m) x = x * unitEndSection a ^ m
  | 0 => by
    show unitEndFun (𝟙 _) x = x * unitEndSection a ^ 0
    rw [unitEndFun_id, pow_zero, mul_one]
  | m + 1 => by
    show unitEndFun (unitEndPow a m ≫ a) x = x * unitEndSection a ^ (m + 1)
    rw [unitEndFun_comp, unitEndFun_eq_mul, unitEndFun_unitEndPow a x m, pow_succ, mul_assoc]

/-- `a^{⊗m} ≫ collapse = collapse ≫ a^{∘m}`. -/
theorem monoidalPowMap_unitEnd_unitPowCollapse
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) : ∀ m : ℕ,
    monoidalPowMap a m ≫ unitPowCollapse Y m = unitPowCollapse Y m ≫ unitEndPow a m
  | 0 => by
    show 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rfl
  | m + 1 => by
    show (monoidalPowMap a m ⊗ₘ a) ≫ ((unitPowCollapse Y m ▷ 𝟙_ Y.Modules) ≫ (λ_ (𝟙_ Y.Modules)).hom) =
      ((unitPowCollapse Y m ▷ 𝟙_ Y.Modules) ≫ (λ_ (𝟙_ Y.Modules)).hom) ≫ (unitEndPow a m ≫ a)
    rw [← tensorHom_id]
    erw [tensorHom_comp_tensorHom_assoc]
    rw [monoidalPowMap_unitEnd_unitPowCollapse a m]
    erw [Category.comp_id]
    have hsplit : (unitPowCollapse Y m ≫ unitEndPow a m) ⊗ₘ a =
        (unitPowCollapse Y m ⊗ₘ 𝟙 (𝟙_ Y.Modules)) ≫ (unitEndPow a m ⊗ₘ a) := by
      erw [tensorHom_comp_tensorHom, Category.id_comp]
    rw [hsplit, Category.assoc, tensorHom_leftUnitor_unit]
    simp only [Category.assoc]

/-- **`liftLocalHomAux` under a change of trivialization**: `Φ^{e₂'}_m = Φ^{e₁'}_m ≫ (e₁'⁻¹ ≫ e₂')^{∘m}`. -/
theorem _root_.AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_unit_scale
    {T W₀ : AlgebraicGeometry.Scheme.{u}} {S : W₀.GradedQCAlgebra} {f : T ⟶ W₀} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e₁' e₂' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) (m : ℕ) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e₂' m =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e₁' m ≫
        unitEndPow (e₁'.inv ≫ e₂'.hom) m := by
  unfold AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux
  have h : e₂'.hom = e₁'.hom ≫ (e₁'.inv ≫ e₂'.hom) := by rw [Iso.hom_inv_id_assoc]
  conv_lhs => rw [h, monoidalPowMap_comp]
  simp only [Category.assoc]
  rw [monoidalPowMap_unitEnd_unitPowCollapse]
  exact rfl

/-- On sections: `Aux(e₂') m a = Aux(e₁') m a * u^m`, with `u = unitEndSection (e₁'⁻¹ ≫ e₂')`. -/
theorem _root_.AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_unit_scale
    {T W₀ : AlgebraicGeometry.Scheme.{u}} {S : W₀.GradedQCAlgebra} {f : T ⟶ W₀} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e₁' e₂' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : W₀.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (m : ℕ) (a : S.sectionsPiece W m) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e₂' W hW m a =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e₁' W hW m a *
        unitEndSection (e₁'.inv ≫ e₂'.hom) ^ m := by
  set g := ι ≫ f with hg
  set η := (pullbackPushforwardAdjunction g).unit.app (S.part m) with hη
  change Hom.app (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e₂' m) ⊤
      (((pullback g).obj (S.part m)).presheaf.map (homOfLE hW).op (η.app W a)) =
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e₁' W hW m a *
      unitEndSection (e₁'.inv ≫ e₂'.hom) ^ m
  rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_unit_scale D ι e₁' e₂' m]
  exact unitEndFun_unitEndPow (e₁'.inv ≫ e₂'.hom)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e₁' W hW m a) m

/-- The section `u = a.hom(1)` corresponding to an isomorphism `a : O_Y ≅ O_Y` is a unit (with inverse `a.inv(1)`). -/
theorem isUnit_unitEndSection_hom (a : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf) :
    IsUnit (unitEndSection a.hom) := by
  refine IsUnit.of_mul_eq_one (unitEndSection a.inv) ?_
  rw [← unitEndFun_eq_mul a.inv (unitEndSection a.hom)]
  change unitEndFun (a.hom ≫ a.inv) 1 = 1
  rw [Iso.hom_inv_id]
  rfl

/-- **Change of trivialization on ring homomorphisms** (the shape needed by `fromOfGlobalSections_unit_scale`):
on a homogeneous element `x` of degree `d`, `Aux(e₂') x = u^d * Aux(e₁') x`. -/
theorem _root_.AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_unit_scale
    {T W₀ : AlgebraicGeometry.Scheme.{u}} {S : W₀.GradedQCAlgebra} {f : T ⟶ W₀} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e₁' e₂' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : W₀.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (d : ℕ) (x : S.sectionsRing W)
    (hx : x ∈ S.sectionsGrading W d) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e₂' W hW x =
      unitEndSection (e₁'.inv ≫ e₂'.hom) ^ d *
        AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e₁' W hW x := by
  obtain ⟨a, rfl⟩ := hx
  rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_of,
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_of,
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_unit_scale D ι e₁' e₂' W hW d a, mul_comm]

/-! ## Transport along an equality of morphisms -/

/-- Transport of `Aux` along `ι = ι'`: the values are unchanged after rebasing the trivialization via
`pullbackCongr`. -/
theorem _root_.AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_congr
    {T W₀ : AlgebraicGeometry.Scheme.{u}} {S : W₀.GradedQCAlgebra} {f : T ⟶ W₀} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) {ι ι' : Y ⟶ T} (h : ι = ι')
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : W₀.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (hW' : (⊤ : Y.Opens) ≤ (ι' ≫ f) ⁻¹ᵁ W) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι'
        (((pullbackCongr h).app M).symm ≪≫ e') W hW' =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e' W hW := by
  subst h
  rfl


end AlgebraicGeometry.Scheme.Modules

end
