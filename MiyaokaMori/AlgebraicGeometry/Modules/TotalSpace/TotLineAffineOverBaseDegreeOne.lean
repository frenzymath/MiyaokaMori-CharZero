import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyLocalRingHom
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator

/-! # The degree-1 component of `projBundle.localRingHom`

Companion of `TotLineAffineOverBase`: the degree-1 analogue of the degree-0
computation `localRingHomComponent_zero_apply` (`ProjectiveBundleUniversalPropertyLocalRingHom`).

Reference: Stacks 01O4 (the morphism to `Proj` determined by an invertible quotient `ψ`: in degree 1 the local
ring homomorphism *is* `ψ` read through the trivialization).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

section DegreeOne

set_option backward.isDefEq.respectTransparency.types false

/-! ### Abstract monoidal lemmas (applied with `exact`, so that no rewriting has to see through
`monoidalPow` / `SheafOfModules.unit` vs `𝟙_`). -/

namespace AlgebraicGeometry.Scheme.projBundle.DegreeOneAux

open CategoryTheory.MonoidalCategory CategoryTheory.Functor.OplaxMonoidal

variable {C : Type*} [Category C] [MonoidalCategory C] {D : Type*} [Category D] [MonoidalCategory D]

/-- `F(λ⁻¹) ≫ δ ≫ η ▷ F W ≫ (𝟙 ⊗ ψ) = ψ ≫ λ⁻¹` (oplax left unitality + naturality of `λ`). -/
theorem oplax_leftUnitor_tensorHom (F : C ⥤ D) [inst : F.OplaxMonoidal] {W : C} {M : D} (ψ : F.obj W ⟶ M) :
    F.map (λ_ W).inv ≫ (δ F (𝟙_ C) W ≫ η F ▷ F.obj W) ≫ (𝟙 (𝟙_ D) ⊗ₘ ψ) = ψ ≫ (λ_ M).inv := by
  rw [← Category.assoc, ← left_unitality, id_tensorHom, leftUnitor_inv_naturality]

/-- `F(λ⁻¹) ≫ δ ≫ η ▷ F M ≫ (𝟙 ⊗ k) ≫ ((𝟙 ▷ 𝟙) ≫ λ) = k`. -/
theorem oplax_leftUnitor_tensorHom_collapse (F : C ⥤ D) [inst : F.OplaxMonoidal] {M : C} {N : D}
    (k : F.obj M ⟶ N) (hN : N = 𝟙_ D) (k' : F.obj M ⟶ 𝟙_ D) (hk : k' = k ≫ eqToHom hN) :
    F.map (λ_ M).inv ≫ (δ F (𝟙_ C) M ≫ η F ▷ F.obj M) ≫ (𝟙 (𝟙_ D) ⊗ₘ k') ≫
      ((𝟙 (𝟙_ D) ▷ 𝟙_ D) ≫ (λ_ (𝟙_ D)).hom) = k' := by
  subst hN
  rw [eqToHom_refl, Category.comp_id] at hk
  subst hk
  rw [← Category.assoc, ← left_unitality, id_tensorHom, id_whiskerRight, Category.id_comp,
    ← Category.assoc, ← leftUnitor_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.projBundle.DegreeOneAux

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.MonoidalCategory

variable {X T : AlgebraicGeometry.Scheme.{u}}

private theorem pullback_map_symGen_comp_symGradedPullbackDesc_one_aux (g : T ⟶ X) (W : X.Modules)
    (hq : W.IsQuasicoherent) {M : T.Modules} [M.IsLineBundle] (ψ : (pullback g).obj W ⟶ M)
    (S : X.GradedQCAlgebra) (hS : S = symGradedAlgebraOfQC W hq)
    (G : W ⟶ S.part 1) (hG : HEq G ((λ_ W).inv ≫ symPowπ W 1))
    (D : (pullback g).obj (S.part 1) ⟶ monoidalPow M 1) (hD : HEq D (symPowPullbackDesc g ψ 1)) :
    (pullback g).map G ≫ D = ψ ≫ (λ_ M).inv := by
  subst hS
  have hG' : G = (λ_ W).inv ≫ symPowπ W 1 := eq_of_heq hG
  have hD' : D = symPowPullbackDesc g ψ 1 := eq_of_heq hD
  subst hG' hD'
  erw [Functor.map_comp, Category.assoc, pullback_map_symPowπ_comp_symPowPullbackDesc]
  show (pullback g).map (λ_ W).inv ≫
      (pullbackTensorObjHom g (𝟙_ X.Modules) W ≫ (pullbackUnitIso g).hom ▷ (pullback g).obj W) ≫
        (𝟙 (𝟙_ T.Modules) ⊗ₘ ψ) = ψ ≫ (λ_ M).inv
  rw [pullbackTensorObjHom_eq_δ, ← pullback_η]
  exact AlgebraicGeometry.Scheme.projBundle.DegreeOneAux.oplax_leftUnitor_tensorHom (pullback g)
    (inst := pullbackOplaxMonoidal g) ψ

/-- **Degree 1 of `symGradedPullbackDesc` is `ψ`**: for `W` quasi-coherent,
`g^*(symGen W) ≫ symGradedPullbackDesc g ψ 1 = ψ ≫ (λ_ M).inv` (target `M^{⊗1} = 𝟙_ ⊗ M`).
Proof: `symGen = (λ_ W).inv ≫ symPowπ W 1` (quasi-coherent branch), `pullback_map_symPowπ_comp_symPowPullbackDesc`,
then the oplax left unitality of `g^*` and the naturality of `λ_`. -/
theorem pullback_map_symGen_comp_symGradedPullbackDesc_one (g : T ⟶ X) (W : X.Modules)
    (hq : W.IsQuasicoherent) {M : T.Modules} [M.IsLineBundle] (ψ : (pullback g).obj W ⟶ M) :
    (pullback g).map (symGen W) ≫ symGradedPullbackDesc g ψ 1 = ψ ≫ (λ_ M).inv := by
  have hS : symGradedAlgebra W = symGradedAlgebraOfQC W hq := by
    delta symGradedAlgebra
    exact dif_pos hq
  have hpart : (symGradedAlgebra W).part 1 = symPow W 1 := by rw [hS]; rfl
  have h1 : symGen W = (λ_ W).inv ≫ symPowπ W 1 ≫ eqToHom hpart.symm := by
    unfold symGen
    rw [dif_pos hq]
  refine pullback_map_symGen_comp_symGradedPullbackDesc_one_aux g W hq ψ _ hS _ ?_ _
    (symGradedPullbackDesc_heq_of_isQuasicoherent g hq ψ 1)
  rw [h1]
  exact heq_comp rfl rfl hpart HEq.rfl (comp_eqToHom_heq _ _)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.projBundle

open AlgebraicGeometry.Scheme.Modules

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- **The degree-1 sheaf-level piece is `ψ` read through the trivialization**:
`g^*(symGen V^∨) ≫ Φ_1 = (pullbackComp ι f).inv.app V^∨ ≫ ι^*ψ ≫ e'.hom`, where `Φ_1 = localRingHomSheafHom … 1`,
`ι = localRingHomIncl f U W`, `g = ι ≫ f`, `e' = localRingHomTriv f M U e W`. -/
theorem pullback_map_symGen_comp_localRingHomSheafHom_one (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (Modules.pullback f).obj (dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens) :
    (Modules.pullback (localRingHomBase f U W)).map (symGen (dual V)) ≫ localRingHomSheafHom V f M ψ U e W 1 =
      (pullbackComp (localRingHomIncl f U W) f).inv.app (dual V) ≫
        (Modules.pullback (localRingHomIncl f U W)).map ψ ≫ (localRingHomTriv f M U e W).hom := by
  have hq : (dual V).IsQuasicoherent :=
    haveI := isLocallyFree_dual' V
    isQuasicoherent_of_isLocallyFree _
  unfold localRingHomSheafHom localRingHomBase
  have E1 := (pullbackComp (localRingHomIncl f U W) f).inv.naturality_assoc (symGen (dual V))
    ((Modules.pullback (localRingHomIncl f U W)).map (symGradedPullbackDesc f ψ 1) ≫
      pullbackMonoidalPow (localRingHomIncl f U W) M 1 ≫
      monoidalPowMap (localRingHomTriv f M U e W).hom 1 ≫ unitPowCollapse _ 1)
  refine E1.trans ?_
  refine congrArg (fun k => _ ≫ k) ?_
  rw [Functor.comp_map, ← Category.assoc, ← Functor.map_comp,
    pullback_map_symGen_comp_symGradedPullbackDesc_one f _ hq ψ]
  erw [Functor.map_comp]
  rw [Category.assoc]
  refine congrArg (fun k => _ ≫ k) ?_
  show (Modules.pullback (localRingHomIncl f U W)).map (λ_ M).inv ≫
      (pullbackTensorObjHom (localRingHomIncl f U W) (𝟙_ T.Modules) M ≫
        (pullbackUnitIso (localRingHomIncl f U W)).hom ▷ (Modules.pullback (localRingHomIncl f U W)).obj M) ≫
      (𝟙 (𝟙_ _) ⊗ₘ (localRingHomTriv f M U e W).hom) ≫
      ((𝟙 (𝟙_ _) ▷ 𝟙_ _) ≫ (λ_ (𝟙_ _)).hom) = (localRingHomTriv f M U e W).hom
  rw [pullbackTensorObjHom_eq_δ, ← pullback_η]
  exact AlgebraicGeometry.Scheme.projBundle.DegreeOneAux.oplax_leftUnitor_tensorHom_collapse
    (Modules.pullback (localRingHomIncl f U W)) (inst := pullbackOplaxMonoidal (localRingHomIncl f U W))
    (localRingHomTriv f M U e W).hom rfl _ (Category.comp_id _).symm

/-- **Degree-1 component on a generator**: for `s ∈ Γ(W, V^∨)`,
`localRingHomComponent … 1 (symGen s) = res_{⊤ ≤ g⁻¹W} ((homEquiv (c ≫ ι^*ψ ≫ e'.hom)).app W s)`
(the degree-1 analogue of `localRingHomComponent_zero_apply`). -/
theorem localRingHomComponent_one_symGen_apply (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (f : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (ψ : (Modules.pullback f).obj (dual V) ⟶ M)
    (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.Opens)
    (s : (dual V).val.obj (op W)) :
    localRingHomComponent V f M ψ U e W 1 (((symGen (dual V)).val.app (op W)).hom s) =
      ((AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit (U ⊓ f ⁻¹ᵁ W).toScheme.ringCatSheaf)).map
          (homOfLE (localRingHomBase_top_le f U W)).op).hom
        ((((pullbackPushforwardAdjunction (localRingHomBase f U W)).homEquiv _ _
            ((pullbackComp (localRingHomIncl f U W) f).inv.app (dual V) ≫
              (Modules.pullback (localRingHomIncl f U W)).map ψ ≫
              (localRingHomTriv f M U e W).hom)).val.app (op W)).hom s) := by
  refine (localRingHomComponent_apply V f M ψ U e W 1 _).trans ?_
  refine (app_top_map_unit_app_eq (localRingHomBase f U W) (localRingHomSheafHom V f M ψ U e W 1) W
    (localRingHomBase_top_le f U W) _).trans ?_
  have h := Adjunction.homEquiv_naturality_left (pullbackPushforwardAdjunction (localRingHomBase f U W))
    (symGen (dual V)) (localRingHomSheafHom V f M ψ U e W 1)
  rw [pullback_map_symGen_comp_localRingHomSheafHom_one] at h
  have h' := congrArg (fun k => (k.val.app (op W)).hom s) h
  refine congrArg _ (Eq.trans ?_ h'.symm)
  rfl

end AlgebraicGeometry.Scheme.projBundle

namespace AlgebraicGeometry.Scheme.Modules

/-- The restriction maps of the structure sheaf viewed as a module are those of the structure sheaf (`rfl`). -/
theorem unit_presheaf_map_apply {Y : AlgebraicGeometry.Scheme.{u}} {U U' : Y.Opens} (h : U ≤ U') (x : Γ(Y, U')) :
    ((AlgebraicGeometry.Scheme.Modules.presheaf (SheafOfModules.unit Y.ringCatSheaf)).map (homOfLE h).op).hom x =
      (Y.presheaf.map (homOfLE h).op).hom x := rfl

/-- The section map `Γ(U, O_Y) → Γ(U, O_Y)` of a morphism `k : O_Y ⟶ O_Y` of modules. -/
def unitHomSections {Y : AlgebraicGeometry.Scheme.{u}}
    (k : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) (x : Γ(Y, U)) : Γ(Y, U) :=
  (k.val.app (op U)).hom x

theorem unitHomSections_mul {Y : AlgebraicGeometry.Scheme.{u}}
    (k : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) (r x : Γ(Y, U)) :
    unitHomSections k U (r * x) = r * unitHomSections k U x :=
  _root_.map_smul (k.val.app (op U)).hom r x

theorem unitHomSections_comp {Y : AlgebraicGeometry.Scheme.{u}}
    (k k' : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) (x : Γ(Y, U)) :
    unitHomSections k' U (unitHomSections k U x) = unitHomSections (k ≫ k') U x := rfl

theorem unitHomSections_id {Y : AlgebraicGeometry.Scheme.{u}} (U : Y.Opens) (x : Γ(Y, U)) :
    unitHomSections (CategoryTheory.CategoryStruct.id (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) U x = x :=
  rfl

/-- An automorphism `k : O_Y ≅ O_Y` of the structure sheaf as a module sends `1 ∈ Γ(U, O)` to a unit:
`k(1) · k⁻¹(1) = k(k⁻¹(1) · 1) = k(k⁻¹(1)) = 1` by linearity. -/
theorem isUnit_unitIso_hom_sections_one {Y : AlgebraicGeometry.Scheme.{u}}
    (k : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) :
    IsUnit (unitHomSections k.hom U 1) := by
  refine IsUnit.of_mul_eq_one (unitHomSections k.inv U 1) ?_
  rw [mul_comm, ← unitHomSections_mul, mul_one, unitHomSections_comp, Iso.inv_hom_id, unitHomSections_id]

end AlgebraicGeometry.Scheme.Modules

end DegreeOne

end
