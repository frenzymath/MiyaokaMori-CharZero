import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.MonoidalPowMulCompat
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertySymPowDesc
import MiyaokaMori.AlgebraicGeometry.Modules.SymPowMap
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackCompMonoidal

/-! # Input data for the lift into a relative Proj and the general local ring map

The input data `LiftData` of `relativeProj.lift` and the general-form local ring homomorphism
`liftLocalRingHomAux`. The construction of `relativeProj.liftLocalRingHom S f M D U e W` only uses "a morphism
`ι : Y → T` and a trivialization `e' : ι^*M ≅ O_Y`"; this file writes it in that generality (`liftLocalHomAux`,
`liftLocalPieceAux`, `liftLocalRingHomAux`), and the definition in `RelativeProjLift.lean` is the special case
`ι = (V ↪ U ↪ T)`, `e' = liftLocalTriv` (by `rfl`). The advantage of the general form: the three compatibilities
needed by `liftLocal_compat` (composition along `j : Y' → Y`, change of `W`, change of trivialization) and
`liftLocalRingHom_map_irrelevant` are stated and proved for a general `(ι, e')`, without repeatedly handling
opens like `U ⊓ f⁻¹W`.

Source: Stacks 01O4, 01N8 (morphisms into a relative Proj). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- The input data of a morphism into a relative Proj (the relative version of Stacks 01O4 / 01N8): `f : T → X`,
   a line bundle `M` on `T`, and graded algebra maps `Ψ_m : f^*S_m → M^{⊗m}` (`M^{⊗m}` the monoidal tensor power
   `monoidalPow`), preserving unit and multiplication and locally surjective in some positive degree. -/

structure AlgebraicGeometry.Scheme.relativeProj.LiftData {X T : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules) where
  Ψ : ∀ m : ℕ, (AlgebraicGeometry.Scheme.Modules.pullback f).obj (S.part m) ⟶
    AlgebraicGeometry.Scheme.Modules.monoidalPow M m
  map_one : (AlgebraicGeometry.Scheme.Modules.pullback f).map S.one ≫ Ψ 0 =
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom
  map_mul : ∀ m n : ℕ, (AlgebraicGeometry.Scheme.Modules.pullback f).map (S.mul m n) ≫ Ψ (m + n) =
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f (S.part m) (S.part n) ≫
      CategoryTheory.MonoidalCategoryStruct.tensorHom (C := T.Modules) (Ψ m) (Ψ n) ≫
      (AlgebraicGeometry.Scheme.Modules.monoidalPowCat M m n).hom
  generates : ∀ t : T, ∃ (U : T.Opens) (_ : t ∈ U) (m : ℕ) (_ : 0 < m),
    CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).map (Ψ m))

/-! ## The local ring homomorphism in general form -/

section LiftLocalRingHomAux

variable {X T Y : AlgebraicGeometry.Scheme.{u}}

/-- The module-sheaf map of the `m`-th component (general form): for `ι : Y → T` and `e' : ι^*M ≅ O_Y`,
`Φ_m := C⁻¹ ≫ ι^*Ψ_m ≫ pullbackMonoidalPow ≫ monoidalPowMap e' ≫ unitPowCollapse : (ι ≫ f)^*S_m ⟶ O_Y`. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (ι ≫ f)).obj (S.part m) ⟶
      SheafOfModules.unit Y.ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app (S.part m) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback ι).map (D.Ψ m) ≫
    AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow ι M m ≫
    AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom m ≫
    AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y m

/-- The section map `Γ(W, S_m) → Γ(Y, O)` on the `m`-th graded piece (general form; requires all of `Y` to lie in
`(ι ≫ f)⁻¹W`). -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (m : ℕ) :
    S.sectionsPiece W m →+ Γ(Y, ⊤) :=
  (((AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m).val.app
      (Opposite.op ⊤)).hom.toAddMonoidHom).comp
    ((((AlgebraicGeometry.Scheme.Modules.pullback (ι ≫ f)).obj (S.part m)).presheaf.map
        (CategoryTheory.homOfLE hW).op).hom.comp
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (ι ≫ f)).unit.app
          (S.part m)).val.app (Opposite.op W)).hom.toAddMonoidHom)

/-! ### Computation of the degree-`0` component

`SheafOfModules.unit` and `𝟙_ T.Modules` are equal only after unfolding a `def`; by default Lean does not unfold
them in the type checks of `rw`/`simp` (Mathlib's `AlgebraicGeometry/Modules/Sheaf.lean` also switches this option
off case by case), so this section disables `backward.isDefEq.respectTransparency.types`. The ingredients
`monoidalPowMap_zero_eq_id`, `unitPowCollapse_zero_eq_id`, `pullbackMonoidalPow_zero_eq_unitIso`,
`app_top_map_unit_app_eq`, `homEquiv_pullbackUnitIso_hom_pbup` come from `ProjectiveBundleUniversalProperty.lean`,
and `pullbackComp_hom_app_pullbackUnitIso_hom` from `ModulesPullbackCompMonoidal.lean`. -/

section ZeroDegree

set_option backward.isDefEq.respectTransparency.types false

/-- **The degree-`0` module map is the unit isomorphism**: `g^*(S.one) ≫ Φ_0 = (pullbackUnitIso g).hom`.
Layer by layer: naturality of `pullbackComp.inv`; `LiftData.map_one` (`f^*(S.one) ≫ Ψ_0 = pullbackUnitIso f`);
the remaining layers are `𝟙` or `pullbackUnitIso ι` in degree `0`; finally
`pullbackComp_hom_app_pullbackUnitIso_hom` composes them into `pullbackUnitIso (ι ≫ f)`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_zero
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (AlgebraicGeometry.Scheme.Modules.pullback
        ((ι ≫ f))).map S.one ≫
        AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' 0 =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        ((ι ≫ f))).hom := by
  unfold AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux
  erw [AlgebraicGeometry.Scheme.Modules.monoidalPowMap_zero_eq_id,
    AlgebraicGeometry.Scheme.Modules.unitPowCollapse_zero_eq_id,
    AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow_zero_eq_unitIso, Category.comp_id]
  have e1 := (AlgebraicGeometry.Scheme.Modules.pullbackComp
      ι f).inv.naturality_assoc S.one
    ((AlgebraicGeometry.Scheme.Modules.pullback
        ι).map (D.Ψ 0) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        ι).hom)
  refine e1.trans ?_
  have e2 : (AlgebraicGeometry.Scheme.Modules.pullback
        ι).map
          ((AlgebraicGeometry.Scheme.Modules.pullback f).map S.one) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback
        ι).map (D.Ψ 0) =
      (AlgebraicGeometry.Scheme.Modules.pullback
        ι).map
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom := by
    rw [← Functor.map_comp, D.map_one]
    exact rfl
  have e3 : (AlgebraicGeometry.Scheme.Modules.pullbackComp
        ι f).inv.app _ ≫
      (AlgebraicGeometry.Scheme.Modules.pullback
        ι).map
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        ι).hom =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        (ι ≫ f)).hom := by
    rw [← AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackUnitIso_hom]
    erw [Iso.inv_hom_id_app_assoc]
  refine Eq.trans ?_ e3
  refine congrArg (fun k => _ ≫ k) ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ _) e2)

/-- Unfolding of the definition of `liftLocalPiece` (`rfl`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_apply
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W)
    (m : ℕ) (s : S.sectionsPiece W m) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW m s =
      ((AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m).val.app (op ⊤)).hom
        (((AlgebraicGeometry.Scheme.Modules.pullback
            ((ι ≫ f))).obj _).presheaf.map
          (homOfLE (hW)).op
          ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
            ((ι ≫ f))).unit.app _).val.app (op W)).hom s)) :=
  rfl

/-- **The value of the degree-`0` component on `S.one.app W r` is `g^♯ r`** (restricted to `⊤ ≤ g⁻¹W`):
`app_top_map_unit_app_eq` turns it into the adjoint transpose of `Φ_0`; `homEquiv_naturality_left` +
`liftLocalHomAux_zero` turn the transpose into `unitToPushforwardObjUnit g`, whose section map is the ring
homomorphism `g^♯` (`rfl`). Shared by `liftLocalPiece_one` (`r = 1`) and `liftLocal_hom`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_zero_apply
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W)
    (r : Γ(X, W)) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW 0 (S.one.app W r) =
      ((ι ≫ f)).appLE W ⊤
        (hW) r := by
  refine (AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_apply D ι e' W hW 0 _).trans ?_
  refine (AlgebraicGeometry.Scheme.Modules.app_top_map_unit_app_eq
    ((ι ≫ f))
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' 0) W
    (hW) _).trans ?_
  have h := Adjunction.homEquiv_naturality_left
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      ((ι ≫ f)))
    S.one (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' 0)
  rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_zero] at h
  erw [AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackUnitIso_hom_pbup] at h
  have h' := congrArg (fun k => (k.val.app (op W)).hom r) h
  refine congrArg _ (Eq.trans ?_ h'.symm)
  rfl

end ZeroDegree

/-- The map assembled from the components preserves `1` (the first hypothesis of `DirectSum.toSemiring`).

Source: Stacks 01O4 / 01N8 (morphisms into a relative Proj are given by graded maps preserving unit and
multiplication).

Proof: the graded unit `GradedMonoid.GOne.one` of `A(W)` is, by definition of `sectionsGCommRing`, `S.one.app W 1`
(`show`); `liftLocalPieceAux_zero_apply` with `r = 1` gives `g^♯ 1`, and a ring homomorphism preserves `1`.
Route of `liftLocalPieceAux_zero_apply`: `LiftData.map_one` says that `Ψ_0` sends the unit of `f^*S_0` to the unit
of `M^{⊗0} = O`; pulling back along `V ↪ T`, `pullbackMonoidalPow`, `monoidalPowMap e'.hom` and `unitPowCollapse`
are the unit isomorphisms of the monoidal structure in degree `0` (`liftLocalHomAux_zero`), so the adjoint
transpose of `Φ_0` is `unitToPushforwardObjUnit g`, i.e. `g^♯` on sections. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_one
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW _
      (GradedMonoid.GOne.one : S.sectionsPiece W 0) = 1 := by
  show AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW 0
    (S.one.app W (1 : Γ(X, W))) = 1
  rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_zero_apply]
  exact map_one _

/-! ### Compatibility with multiplication

Ingredients: `pullbackMonoidalPow_monoidalPowCat`, `unitPowCollapse_monoidalPowCat` and
`MonoidalPowAux.map_tensorHom_δ_comp` from `MonoidalPowMulCompat.lean`, `monoidalPowCat_monoidalPowMap` from
`SymPowMap.lean`, and `pullbackComp_hom_app_pullbackTensorObjHom` from `ModulesPullbackCompMonoidal.lean`. -/

section LiftLocalHomMul

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.MonoidalCategory

/-- Compatibility of `pullbackComp.inv` with the comparison map `δ` (the inverse version of
`pullbackComp_hom_app_pullbackTensorObjHom`, with a tail):
`C⁻¹_{A⊗B} ≫ ι^*δ_f ≫ δ_ι ≫ (a ⊗ a') ≫ h = δ_{ι≫f} ≫ ((C⁻¹_A ≫ a) ⊗ (C⁻¹_B ≫ a')) ≫ h`. -/
private theorem pullbackComp_inv_app_δ_comp_rpl {X₀ Y₀ Z₀ : AlgebraicGeometry.Scheme.{u}}
    (ι : X₀ ⟶ Y₀) (f : Y₀ ⟶ Z₀) (A B : Z₀.Modules) {A' B' E : X₀.Modules}
    (a : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj A) ⟶ A')
    (a' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj B) ⟶ B')
    (h : A' ⊗ B' ⟶ E) :
    (AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app (A ⊗ B) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback ι).map
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f A B) ≫
        AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ι _ _ ≫ (a ⊗ₘ a') ≫ h =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (ι ≫ f) A B ≫
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app A ≫ a) ⊗ₘ
          ((AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app B ≫ a')) ≫ h := by
  have hD := AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_pullbackTensorObjHom ι f A B
  have hs : (a ⊗ₘ a') =
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).hom.app A ⊗ₘ
        (AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).hom.app B) ≫
      (((AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app A ≫ a) ⊗ₘ
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app B ≫ a')) := by
    rw [tensorHom_comp_tensorHom, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  rw [hs]
  simp only [Category.assoc]
  rw [← reassoc_of% hD, Iso.inv_hom_id_app_assoc]

variable {V' : AlgebraicGeometry.Scheme.{u}}

/-- **Claim M (general form)**: for any `ι : V' → T` and `e' : ι^*M ≅ O_{V'}`, writing
`Φ_k := C⁻¹ ≫ ι^*Ψ_k ≫ pullbackMonoidalPow ≫ monoidalPowMap e' ≫ unitPowCollapse`, one has
`(ι≫f)^*(S.mul m n) ≫ Φ_{m+n} = δ ≫ (Φ_m ⊗ Φ_n) ≫ (λ_ O).hom`.
Layer by layer: naturality of `pullbackComp.inv`; `LiftData.map_mul`; (A) `pullbackMonoidalPow_monoidalPowCat`;
(B) `monoidalPowCat_monoidalPowMap`; (C) `unitPowCollapse_monoidalPowCat`; naturality of `δ`
(`map_tensorHom_δ_comp`); compatibility of `pullbackComp` with `δ`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_mul
    (ι : V' ⟶ T) (S : X.GradedQCAlgebra) (f : T ⟶ X) (M : T.Modules)
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit V'.ringCatSheaf)
    (m n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (ι ≫ f)).map (S.mul m n) ≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app (S.part (m + n)) ≫
          (AlgebraicGeometry.Scheme.Modules.pullback ι).map (D.Ψ (m + n)) ≫
          AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow ι M (m + n) ≫
          AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom (m + n) ≫
          AlgebraicGeometry.Scheme.Modules.unitPowCollapse V' (m + n)) =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (ι ≫ f) (S.part m) (S.part n) ≫
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app (S.part m) ≫
          (AlgebraicGeometry.Scheme.Modules.pullback ι).map (D.Ψ m) ≫
          AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow ι M m ≫
          AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom m ≫
          AlgebraicGeometry.Scheme.Modules.unitPowCollapse V' m) ⊗ₘ
         ((AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app (S.part n) ≫
          (AlgebraicGeometry.Scheme.Modules.pullback ι).map (D.Ψ n) ≫
          AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow ι M n ≫
          AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom n ≫
          AlgebraicGeometry.Scheme.Modules.unitPowCollapse V' n)) ≫
        (λ_ (𝟙_ V'.Modules)).hom := by
  have h1 : (AlgebraicGeometry.Scheme.Modules.pullback (ι ≫ f)).map (S.mul m n) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app (S.part (m + n)) =
      (AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app (S.part m ⊗ S.part n) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback ι).map
          ((AlgebraicGeometry.Scheme.Modules.pullback f).map (S.mul m n)) :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.naturality (S.mul m n)
  have h2 : (AlgebraicGeometry.Scheme.Modules.pullback ι).map
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map (S.mul m n)) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback ι).map (D.Ψ (m + n)) =
      (AlgebraicGeometry.Scheme.Modules.pullback ι).map
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f (S.part m) (S.part n)) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback ι).map (D.Ψ m ⊗ₘ D.Ψ n) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback ι).map
          (AlgebraicGeometry.Scheme.Modules.monoidalPowCat M m n).hom := by
    rw [← Functor.map_comp, D.map_mul, Functor.map_comp, Functor.map_comp]
  have h3 := AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow_monoidalPowCat_assoc ι M m n
    (AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom (m + n) ≫
      AlgebraicGeometry.Scheme.Modules.unitPowCollapse V' (m + n))
  have h4 : (AlgebraicGeometry.Scheme.Modules.monoidalPowCat
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M) m n).hom ≫
        AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom (m + n) ≫
        AlgebraicGeometry.Scheme.Modules.unitPowCollapse V' (m + n) =
      (AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom m ⊗ₘ
          AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom n) ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowCat (𝟙_ V'.Modules) m n).hom ≫
        AlgebraicGeometry.Scheme.Modules.unitPowCollapse V' (m + n) :=
    ((reassoc_of% (AlgebraicGeometry.Scheme.Modules.monoidalPowCat_monoidalPowMap e'.hom m n)) _).symm
  have h5 := AlgebraicGeometry.Scheme.Modules.unitPowCollapse_monoidalPowCat V' m n
  have h6 : (AlgebraicGeometry.Scheme.Modules.pullback ι).map (D.Ψ m ⊗ₘ D.Ψ n) ≫
        AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ι
          (AlgebraicGeometry.Scheme.Modules.monoidalPow M m)
          (AlgebraicGeometry.Scheme.Modules.monoidalPow M n) ≫
        ((AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow ι M m ≫
            AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom m ≫
            AlgebraicGeometry.Scheme.Modules.unitPowCollapse V' m) ⊗ₘ
          (AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow ι M n ≫
            AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom n ≫
            AlgebraicGeometry.Scheme.Modules.unitPowCollapse V' n)) ≫
        (λ_ (𝟙_ V'.Modules)).hom =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ι
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (S.part m))
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (S.part n)) ≫
        (((AlgebraicGeometry.Scheme.Modules.pullback ι).map (D.Ψ m) ≫
            AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow ι M m ≫
            AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom m ≫
            AlgebraicGeometry.Scheme.Modules.unitPowCollapse V' m) ⊗ₘ
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).map (D.Ψ n) ≫
            AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow ι M n ≫
            AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom n ≫
            AlgebraicGeometry.Scheme.Modules.unitPowCollapse V' n)) ≫
        (λ_ (𝟙_ V'.Modules)).hom :=
    AlgebraicGeometry.Scheme.Modules.MonoidalPowAux.map_tensorHom_δ_comp
      (AlgebraicGeometry.Scheme.Modules.pullback ι) (D.Ψ m) (D.Ψ n) _ _ _
  rw [reassoc_of% h1, reassoc_of% h2, h3, h4, h5, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  refine (congrArg (fun k => (AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app
    (S.part m ⊗ S.part n) ≫ (AlgebraicGeometry.Scheme.Modules.pullback ι).map
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f (S.part m) (S.part n)) ≫ k) h6).trans ?_
  exact pullbackComp_inv_app_δ_comp_rpl ι f (S.part m) (S.part n) _ _ _


/-- `liftLocalHomAux_mul` folded through `liftLocalHomAux` (by unfolding the definition). -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_mul'
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (m n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (ι ≫ f)).map (S.mul m n) ≫
        AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' (m + n) =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom (ι ≫ f) (S.part m) (S.part n) ≫
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m ⊗ₘ
          AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n) ≫
        (λ_ (𝟙_ Y.Modules)).hom :=
  AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_mul ι S f M D e' m n

end LiftLocalHomMul

/-- The map assembled from the components preserves multiplication (the second hypothesis of
`DirectSum.toSemiring`).

Source: Stacks 01O4 / 01N8.

Proof: the graded multiplication of `A(W)` is `GMul.mul a b = S.sectionsGMul W a b = (S.mul m n).app W (a ⊗ b)`.
`app_top_map_unit_app_eq` turns the values of the three `liftLocalPiece` into "the adjoint transpose evaluated on
`W`, then restricted to `⊤`"; `homEquiv_naturality_left` turns `homEquiv Φ_{m+n}` applied to `mul(a⊗b)` into
`homEquiv (g^*mul ≫ Φ_{m+n})` applied to `a ⊗ b`; **Claim M** (`liftLocalHom_mul`) says
`g^*mul ≫ Φ_{m+n} = δ_g ≫ (Φ_m ⊗ Φ_n) ≫ λ_O`; `homEquiv_naturality_right` +
`homEquiv_pullbackTensorObjHom_tensorSections` (the transpose of `δ` sends `a ⊗ b` to `η a ⊗ η b`) +
`tensorHom_tensorSections` + `leftUnitor_app_tensorSections` (`λ_O` on `r ⊗ s` is `r • s = r * s`); finally the
restriction map is a ring homomorphism and preserves multiplication. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_mul
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) :
    ∀ {m n : ℕ} (a : S.sectionsPiece W m) (b : S.sectionsPiece W n),
      AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW _
          (GradedMonoid.GMul.mul a b) =
        AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW _ a *
          AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW _ b := by
  intro m n a b
  have hgW := hW
  -- the values of the three liftLocalPiece: adjoint transpose evaluated on W, then restricted
  have L := AlgebraicGeometry.Scheme.Modules.app_top_map_unit_app_eq ((ι ≫ f))
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' (m + n)) W hgW ((S.mul m n).app W (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) W a b))
  have Ra := AlgebraicGeometry.Scheme.Modules.app_top_map_unit_app_eq ((ι ≫ f)) (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m) W hgW a
  have Rb := AlgebraicGeometry.Scheme.Modules.app_top_map_unit_app_eq ((ι ≫ f)) (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n) W hgW b
  show AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW (m + n)
      ((S.mul m n).app W (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) W a b)) =
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW m a *
      AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW n b
  refine ((AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_apply D ι e' W hW (m + n) _).trans L).trans
    (Eq.trans ?_ (congrArg₂ (· * ·)
      ((AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_apply D ι e' W hW m a).trans Ra)
      ((AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_apply D ι e' W hW n b).trans Rb)).symm)
  -- the restriction map is a ring homomorphism
  have hres : ∀ x y : Γ(Y, ((ι ≫ f)) ⁻¹ᵁ W),
      (show Γ(Y, ⊤) from ((AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit Y.ringCatSheaf)).map (homOfLE hgW).op) (x * y)) =
        (show Γ(Y, ⊤) from ((AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit Y.ringCatSheaf)).map (homOfLE hgW).op) x) *
        (show Γ(Y, ⊤) from ((AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit Y.ringCatSheaf)).map (homOfLE hgW).op) y) :=
    fun x y => map_mul (Y.presheaf.map (homOfLE hgW).op).hom x y
  refine Eq.trans (congrArg _ ?_) (hres _ _)
  -- core: transpose of Φ_{m+n} on mul(a⊗b) = (transpose of Φ_m on a) · (transpose of Φ_n on b)
  have k1 : (show Γ(Y, ((ι ≫ f)) ⁻¹ᵁ W) from ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).homEquiv _ _ (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' (m + n))).val.app (op W)).hom ((S.mul m n).app W (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) W a b))) =
      (show Γ(Y, ((ι ≫ f)) ⁻¹ᵁ W) from ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).homEquiv _ _ ((AlgebraicGeometry.Scheme.Modules.pullback ((ι ≫ f))).map (S.mul m n) ≫
          (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' (m + n)))).val.app (op W)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) W a b)) :=
    (congrArg (fun k => (k.val.app (op W)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) W a b))
      (Adjunction.homEquiv_naturality_left (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f))) (S.mul m n) (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' (m + n)))).symm
  have k2 := AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux_mul' D ι e' m n
  have k3 := Adjunction.homEquiv_naturality_right (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ((ι ≫ f)) (S.part m) (S.part n))
    (((AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m) ⊗ₘ (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n)) ≫ (λ_ (𝟙_ Y.Modules)).hom)
  have k4 := AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackTensorObjHom_tensorSections ((ι ≫ f))
    (S.part m) (S.part n) W a b
  have k5 := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m) (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n) (((ι ≫ f)) ⁻¹ᵁ W)
    (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).unit.app (S.part m)).val.app (op W)).hom a) (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).unit.app (S.part n)).val.app (op W)).hom b)
  have k6 := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections
    (𝟙_ Y.Modules) (((ι ≫ f)) ⁻¹ᵁ W)
    (((AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m).val.app (op (((ι ≫ f)) ⁻¹ᵁ W))).hom (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).unit.app (S.part m)).val.app (op W)).hom a))
    (((AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n).val.app (op (((ι ≫ f)) ⁻¹ᵁ W))).hom (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).unit.app (S.part n)).val.app (op W)).hom b))
  have ra : (show Γ(Y, ((ι ≫ f)) ⁻¹ᵁ W) from ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).homEquiv _ _ (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m)).val.app (op W)).hom a) =
      (show Γ(Y, ((ι ≫ f)) ⁻¹ᵁ W) from ((AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m).val.app (op (((ι ≫ f)) ⁻¹ᵁ W))).hom (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).unit.app (S.part m)).val.app (op W)).hom a)) :=
    congrArg (fun k => (k.val.app (op W)).hom a) (Adjunction.homEquiv_unit (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f))) _ _ (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m))
  have rb : (show Γ(Y, ((ι ≫ f)) ⁻¹ᵁ W) from ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).homEquiv _ _ (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n)).val.app (op W)).hom b) =
      (show Γ(Y, ((ι ≫ f)) ⁻¹ᵁ W) from ((AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n).val.app (op (((ι ≫ f)) ⁻¹ᵁ W))).hom (((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).unit.app (S.part n)).val.app (op W)).hom b)) :=
    congrArg (fun k => (k.val.app (op W)).hom b) (Adjunction.homEquiv_unit (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f))) _ _ (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n))
  refine k1.trans (Eq.trans ?_ (congrArg₂ (fun x y : Γ(Y, ((ι ≫ f)) ⁻¹ᵁ W) => x * y) ra rb).symm)
  refine Eq.trans ?_ (smul_eq_mul _ _)
  refine Eq.trans ?_ k6
  refine Eq.trans ?_ (congrArg _ k5)
  refine Eq.trans (congrArg (fun z => ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ((ι ≫ f)))).homEquiv _ _ z).val.app (op W)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) W a b)) k2) ?_
  refine Eq.trans (congrArg (fun z => (z.val.app (op W)).hom (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) W a b)) k3) ?_
  exact congrArg (fun z => ((λ_ (𝟙_ Y.Modules)).hom.val.app (op (((ι ≫ f)) ⁻¹ᵁ W))).hom
    ((((AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' m) ⊗ₘ (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n)).val.app (op (((ι ≫ f)) ⁻¹ᵁ W))).hom z)) k4


/-- The local ring homomorphism `A(W) = ⊕_m Γ(W, S_m) →+* Γ(Y, O)` in general form (`DirectSum.toSemiring`). -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) :
    S.sectionsRing W →+* Γ(Y, ⊤) :=
  DirectSum.toSemiring
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_one D ι e' W hW)
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_mul D ι e' W hW)

/-- The value of `liftLocalRingHomAux` on an element `of m a` of the `m`-th piece is `liftLocalPieceAux m a`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_of
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (m : ℕ) (a : S.sectionsPiece W m) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e' W hW
        (DirectSum.of (S.sectionsPiece W) m a) =
      AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW m a :=
  DirectSum.toSemiring_of _ _ _ m a

/-- The value of `liftLocalRingHomAux` on the structure map `sectionsUnit W r` (degree-`0` piece) is `(ι ≫ f)^♯ r`
restricted to `⊤`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux_sectionsUnit
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M) (ι : Y ⟶ T)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (r : Γ(X, W)) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalRingHomAux D ι e' W hW ((S.sectionsUnit W r).1) =
      (ι ≫ f).appLE W ⊤ hW r := by
  show DirectSum.toSemiring _ _ _ (DirectSum.of (S.sectionsPiece W) 0 (S.one.app W r)) = _
  exact (DirectSum.toSemiring_of _ _ _ 0 _).trans
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_zero_apply D ι e' W hW r)

end LiftLocalRingHomAux

end
