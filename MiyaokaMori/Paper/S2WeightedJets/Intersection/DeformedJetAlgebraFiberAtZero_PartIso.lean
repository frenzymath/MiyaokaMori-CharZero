import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_Construction
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalPreadditive
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackUnitMul
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraSyzygy

/-! # The fibre at `λ = 0` of a Rees piece is the associated graded piece

`(s₀^*R)_j ≅ ⊕_{p ≤ j} I^{(p)}_j / I^{(p+1)}_j` for the Rees deformation `R = S.reesDeformation` of any graded
quasi-coherent algebra `S` (Stacks 052P: `R/λR = gr_I(A)`), together with the named isomorphism
`reesDeformation.partIsoGr` used by the algebra-level statement through `DeformedJetAlgebraFiberAtZero_Generators` /
`DeformedJetAlgebraFiberAtZero_MulCompat`. This is part of "removing the nonlinear terms" in Lemma 2.3 of the paper.

Structure:
* §0: along `λ = 0` every positive power `λ^{e+1}` pulls back to `0` (`sectionAt_zero_appTop_coord_pow_succ`),
  `unitMul 0 = 0`, hence `s₀^*(mulCoordPow (e+1) M) = 0` (`pullback_sectionAt_zero_map_mulCoordPow_succ`).
* §0a (generic abelian category): `isoOfEpiFactor`, `cokernelBiproductMapIso`, `map_ι_comp_mapBiproduct_hom`.
* §1c: along `λ = 0`, `s₀^*ψ_j = ⊕_e stepHom (j-e) j` (`pullbackSectionAtBiproductIso_inv_comp_map_syzygy`),
  `s₀^*R_j = coker (s₀^*(ker gen))` (`pullbackSectionAtZeroPartIsoCokernel`), and `coker (s₀^*ψ_j) ≅ coker (s₀^*(ker gen))`
  (`cokernelMapSyzygyIsoCokernelMapKernelι`), whose non-formal input `reesDeformation.map_kernel_ι_comp_cokernel_π_map_syzygy`
  follows from the exactness of the syzygy sequence (`DeformedJetAlgebraSyzygy`).
* §2: `reesDeformation.partIsoGr` (data) and `reesDeformation_restrictToLambda_zero_part_iso`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v₁ u₁

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-! ## §0 Along `λ = 0`, positive powers of `λ` pull back to `0` -/

/-- Along `λ = 0`, every positive power `λ^{e+1}` pulls back to `0` (`AffineSpace.homOfVector_appTop_coord`:
`s₀^♯ λ = (X ↘ Spec k)^♯ (ΓSpecIso k)⁻¹ 0 = 0`). Companion of `sectionAt_one_appTop_coord_pow`. -/
theorem AlgebraicGeometry.Scheme.affineLineOver.sectionAt_zero_appTop_coord_pow_succ {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (e : ℕ) :
    (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (0 : k)).appTop
        ((AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
          Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) ^ (e + 1)) = 0 := by
  refine (map_pow ((AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (0 : k)).appTop).hom
    (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
      Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) (e + 1)).trans ?_
  have h : (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (0 : k)).appTop
      (AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1))) =
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv (0 : k)) :=
    AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord _ _ _
  refine (congrArg (· ^ (e + 1)) h).trans ?_
  simp only [map_zero, zero_pow (Nat.succ_ne_zero e)]

/-- `unitMul 0 = 0`: multiplication by the global function `0` is the zero endomorphism of `O_X`
(`unitHomEquiv` is injective; both sides correspond to the family of sections `U ↦ 0`). Companion of `unitMul_one`. -/
theorem AlgebraicGeometry.Scheme.Modules.unitMul_zero {X : AlgebraicGeometry.Scheme.{u}} :
    AlgebraicGeometry.Scheme.Modules.unitMul (X := X) (0 : Γ(X, ⊤)) = 0 := by
  unfold AlgebraicGeometry.Scheme.Modules.unitMul
  rw [Equiv.symm_apply_eq]
  ext U
  rw [SheafOfModules.unitHomEquiv_apply_coe]
  show (X.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op).hom 0 =
    (((0 : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)).val.app U).hom
      (1 : X.ringCatSheaf.obj.obj U)
  rw [map_zero]
  rfl

/-- **Key input for the fibre at `λ = 0`**: the pullback along `s₀ = sectionAt X 0` of multiplication by a positive
power `λ^{e+1}` is `0` (`pullback_map_unitScalar` + `sectionAt_zero_appTop_coord_pow_succ` + `unitMul_zero` +
`zero_whiskerRight'`). Companion of `pullback_sectionAt_one_map_mulCoordPow`. -/
theorem AlgebraicGeometry.Scheme.affineLineOver.pullback_sectionAt_zero_map_mulCoordPow_succ {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (e : ℕ)
    (M : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (0 : k))).map
        (AlgebraicGeometry.Scheme.affineLineOver.mulCoordPow (e + 1) M) = 0 := by
  have h := AlgebraicGeometry.Scheme.Modules.pullback_map_unitScalar
    (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (0 : k))
    ((AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
      Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) ^ (e + 1)) M
  refine h.trans ?_
  have hz : (show 𝟙_ X.Modules ⟶ 𝟙_ X.Modules from AlgebraicGeometry.Scheme.Modules.unitMul
      ((AlgebraicGeometry.Scheme.affineLineOver.sectionAt X (0 : k)).appTop
        ((AlgebraicGeometry.AffineSpace.coord X (⟨0⟩ : ULift.{u} (Fin 1)) :
          Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤)) ^ (e + 1)))) = 0 := by
    rw [AlgebraicGeometry.Scheme.affineLineOver.sectionAt_zero_appTop_coord_pow_succ]
    exact AlgebraicGeometry.Scheme.Modules.unitMul_zero
  rw [hz, AlgebraicGeometry.Scheme.Modules.zero_whiskerRight', zero_comp, comp_zero]

/-! ## §0a Generic categorical lemmas: cokernels and finite biproducts in an abelian category -/

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

-- `HasBiproduct` is a `Prop`, so this local instance is interchangeable with the one `X.Modules` carries.
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- Two epimorphisms `p : A ⟶ B`, `q : A ⟶ B'` out of the same object that factor through each other
(`p ≫ u = q`, `q ≫ v = p`) have isomorphic targets (the "two cokernel projections" argument). -/
def isoOfEpiFactor {A B B' : C} (p : A ⟶ B) (q : A ⟶ B') [Epi p] [Epi q] (u : B ⟶ B') (v : B' ⟶ B)
    (hu : p ≫ u = q) (hv : q ≫ v = p) : B ≅ B' where
  hom := u
  inv := v
  hom_inv_id := by rw [← cancel_epi p, ← Category.assoc, hu, hv, Category.comp_id]
  inv_hom_id := by rw [← cancel_epi q, ← Category.assoc, hv, hu, Category.comp_id]

/-- `coker (⊕_e f_e) ≅ ⊕_e coker f_e` for a finite family `f_e : A_e ⟶ B_e`. -/
def cokernelBiproductMapIso {J : Type} [Fintype J] {A B : J → C} (f : ∀ e, A e ⟶ B e) :
    cokernel (biproduct.map f) ≅ ⨁ (fun e => cokernel (f e)) where
  hom := cokernel.desc _ (biproduct.map fun e => cokernel.π (f e)) (by
    apply biproduct.hom_ext'
    intro e
    rw [biproduct.ι_map_assoc, biproduct.ι_map, cokernel.condition_assoc, zero_comp, comp_zero])
  inv := biproduct.desc fun e => cokernel.desc (f e) (biproduct.ι B e ≫ cokernel.π (biproduct.map f)) (by
    rw [← Category.assoc, ← biproduct.ι_map, Category.assoc, cokernel.condition, comp_zero])
  hom_inv_id := by
    rw [← cancel_epi (cokernel.π (biproduct.map f)), cokernel.π_desc_assoc, Category.comp_id]
    apply biproduct.hom_ext'
    intro e
    rw [biproduct.ι_map_assoc, biproduct.ι_desc, cokernel.π_desc]
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro e
    rw [biproduct.ι_desc_assoc, Category.comp_id, ← cancel_epi (cokernel.π (f e)), cokernel.π_desc_assoc,
      Category.assoc, cokernel.π_desc, biproduct.ι_map]

/-- `F(ι_e) ≫ (F.mapBiproduct f).hom = ι_e` for an additive functor. -/
theorem map_ι_comp_mapBiproduct_hom {D : Type*} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] {J : Type} (f : J → C) [HasBiproduct f] [HasBiproduct (F.obj ∘ f)]
    [PreservesBiproduct f F] (e : J) :
    F.map (biproduct.ι f e) ≫ (F.mapBiproduct f).hom = biproduct.ι (F.obj ∘ f) e := by
  rw [← biproduct.ι_desc (fun j => F.map (biproduct.ι f j)) e, ← Functor.mapBiproduct_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end CategoryTheory.Limits

/-! §1, §1a, §1b (`landsIn_irrelevantPow_succ`, `irrelevantPow.stepHom`, `irrelevantPow_isZero_of_lt`, the syzygy `ψ_j` and
`syzygy_comp_gen`) live in `DeformedJetAlgebraSyzygy`, which also proves that the syzygy sequence is exact
(`reesDeformation.exact_syzygy_gen`). -/

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-! ## §1c Along `λ = 0`: `s₀^*ψ_j = ⊕_e stepHom (j-e) j` and `s₀^*R_j` as a cokernel

Write `F := s₀^*` (`s₀ = sectionAt X 0`) and `π^*` for the pullback along `toBase X`. `F ∘ π^* ≅ 𝟭` since `s₀ ≫ π = 𝟙`;
`F` is additive (left adjoint) and preserves finite colimits, so `F(⊕_e π^*M_e) ≅ ⊕_e M_e` and `F(R_j) = F(Im gen) =
coker (F(ker gen) → F(⊕ π^*I))` (an epimorphism is the cokernel of its kernel, `Abelian.epiIsCokernelOfKernel`).
The `λ`-terms of `ψ_j` die (`pullback_sectionAt_zero_map_mulCoordPow_succ`), so `F ψ_j` becomes `⊕_e stepHom (j-e) j`
with cokernel `⊕_e I^{(j-e)}_j/I^{(j-e+1)}_j`. Since `ψ_j` factors through `ker gen`, `coker (F ψ_j)` maps onto `F(R_j)`;
the converse (`F(ker gen)` maps to zero in `coker (F ψ_j)`, i.e. `ker gen = Im ψ_j + λ·ker gen`) is the local statement
`map_kernel_ι_comp_cokernel_π_map_syzygy`. -/

namespace reesDeformation

variable {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- `s_t^* ∘ π^* ≅ 𝟭` (`pullbackComp`, `s_t ≫ π = 𝟙` (`AffineSpace.homOfVector_over`), `pullbackId`). -/
noncomputable def pullbackToBaseCompPullbackSectionAtIso (t : k) :
    Modules.pullback (affineLineOver.toBase X) ⋙ Modules.pullback (affineLineOver.sectionAt X t) ≅
      𝟭 X.Modules :=
  Modules.pullbackComp (affineLineOver.sectionAt X t) (affineLineOver.toBase X) ≪≫
    eqToIso (congrArg Modules.pullback (AlgebraicGeometry.AffineSpace.homOfVector_over _ _ :
      affineLineOver.sectionAt X t ≫ affineLineOver.toBase X = 𝟙 X)) ≪≫
    Modules.pullbackId X

@[reassoc]
theorem map_map_comp_pullbackToBaseCompPullbackSectionAtIso_hom_app (t : k) {A B : X.Modules} (f : A ⟶ B) :
    (Modules.pullback (affineLineOver.sectionAt X t)).map ((Modules.pullback (affineLineOver.toBase X)).map f) ≫
        (pullbackToBaseCompPullbackSectionAtIso (X := X) t).hom.app B =
      (pullbackToBaseCompPullbackSectionAtIso (X := X) t).hom.app A ≫ f :=
  (pullbackToBaseCompPullbackSectionAtIso (X := X) t).hom.naturality f

theorem pullbackSectionAt_additive (t : k) : (Modules.pullback (affineLineOver.sectionAt X t)).Additive :=
  (Modules.pullbackPushforwardAdjunction _).left_adjoint_additive

/-- `s_t^*(⊕_e π^*M_e) ≅ ⊕_e M_e` (`Functor.mapBiproduct` + `pullbackToBaseCompPullbackSectionAtIso`). -/
noncomputable def pullbackSectionAtBiproductIso (t : k) {J : Type} [Fintype J] (M : J → X.Modules) :
    (Modules.pullback (affineLineOver.sectionAt X t)).obj
        (⨁ fun e => (Modules.pullback (affineLineOver.toBase X)).obj (M e)) ≅ ⨁ M :=
  have := pullbackSectionAt_additive (X := X) t
  Functor.mapBiproduct _ _ ≪≫
    CategoryTheory.Limits.biproduct.mapIso fun e => (pullbackToBaseCompPullbackSectionAtIso (X := X) t).app (M e)

theorem ι_comp_pullbackSectionAtBiproductIso_inv (t : k) {J : Type} [Fintype J] (M : J → X.Modules) (e : J) :
    CategoryTheory.Limits.biproduct.ι M e ≫ (pullbackSectionAtBiproductIso (X := X) t M).inv =
      (pullbackToBaseCompPullbackSectionAtIso (X := X) t).inv.app (M e) ≫
        (Modules.pullback (affineLineOver.sectionAt X t)).map
          (CategoryTheory.Limits.biproduct.ι (fun e => (Modules.pullback (affineLineOver.toBase X)).obj (M e)) e) := by
  have := pullbackSectionAt_additive (X := X) t
  unfold pullbackSectionAtBiproductIso
  rw [Iso.trans_inv, CategoryTheory.Limits.biproduct.mapIso_inv, ← Category.assoc,
    CategoryTheory.Limits.biproduct.ι_map, Category.assoc, Functor.mapBiproduct_inv,
    CategoryTheory.Limits.biproduct.ι_desc]
  rfl

theorem map_ι_comp_pullbackSectionAtBiproductIso_hom (t : k) {J : Type} [Fintype J] (M : J → X.Modules) (e : J) :
    (Modules.pullback (affineLineOver.sectionAt X t)).map
        (CategoryTheory.Limits.biproduct.ι (fun e => (Modules.pullback (affineLineOver.toBase X)).obj (M e)) e) ≫
        (pullbackSectionAtBiproductIso (X := X) t M).hom =
      (pullbackToBaseCompPullbackSectionAtIso (X := X) t).hom.app (M e) ≫ CategoryTheory.Limits.biproduct.ι M e := by
  have := pullbackSectionAt_additive (X := X) t
  unfold pullbackSectionAtBiproductIso
  rw [Iso.trans_hom, ← Category.assoc, CategoryTheory.Limits.map_ι_comp_mapBiproduct_hom,
    CategoryTheory.Limits.biproduct.mapIso_hom, CategoryTheory.Limits.biproduct.ι_map]
  rfl

/-- Along `λ = 0` the `λ`-part of the syzygy dies (`pullback_sectionAt_zero_map_mulCoordPow_succ`). -/
theorem pullback_sectionAt_zero_map_syzygyLam (j : ℕ) (e : Fin (j + 1)) :
    (Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (syzygyLam S j e) = 0 := by
  have := pullbackSectionAt_additive (X := X) (0 : k)
  obtain ⟨e, he⟩ := e
  cases e with
  | zero => rw [syzygyLam_zero, Functor.map_zero]
  | succ e' =>
    rw [syzygyLam_succ, Functor.map_comp]
    have h0 := affineLineOver.pullback_sectionAt_zero_map_mulCoordPow_succ (k := k) 0
      ((Modules.pullback (affineLineOver.toBase X)).obj (S.irrelevantPow (j - (e' + 1) + 1) j).1)
    rw [h0, zero_comp]

/-- **`s₀^*ψ_j = ⊕_e stepHom (j-e) j`** under the identifications `s₀^*(⊕ π^*M) ≅ ⊕ M`. -/
theorem pullbackSectionAtBiproductIso_inv_comp_map_syzygy (j : ℕ) :
    (pullbackSectionAtBiproductIso (X := X) (0 : k) (fun e : Fin (j + 1) => (S.irrelevantPow (j - e.1 + 1) j).1)).inv ≫
        (Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (syzygy S j) ≫
        (pullbackSectionAtBiproductIso (X := X) (0 : k) (fun e : Fin (j + 1) => (S.irrelevantPow (j - e.1) j).1)).hom =
      CategoryTheory.Limits.biproduct.map fun e : Fin (j + 1) => irrelevantPow.stepHom S (j - e.1) j := by
  have := pullbackSectionAt_additive (X := X) (0 : k)
  apply CategoryTheory.Limits.biproduct.hom_ext'
  intro e
  rw [CategoryTheory.Limits.biproduct.ι_map, ← Category.assoc, ι_comp_pullbackSectionAtBiproductIso_inv,
    Category.assoc, ← Functor.map_comp_assoc, ι_syzygy, Functor.map_sub, pullback_sectionAt_zero_map_syzygyLam,
    sub_zero, Functor.map_comp, Category.assoc, map_ι_comp_pullbackSectionAtBiproductIso_hom,
    map_map_comp_pullbackToBaseCompPullbackSectionAtIso_hom_app_assoc, Iso.inv_hom_id_app_assoc]

/-- `coker (s₀^*ψ_j) ≅ coker (⊕_e stepHom (j-e) j)`. -/
noncomputable def cokernelPullbackSyzygyIso (j : ℕ) :
    CategoryTheory.Limits.cokernel ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (syzygy S j)) ≅
      CategoryTheory.Limits.cokernel
        (CategoryTheory.Limits.biproduct.map fun e : Fin (j + 1) => irrelevantPow.stepHom S (j - e.1) j) :=
  CategoryTheory.Limits.cokernel.mapIso _ _ (pullbackSectionAtBiproductIso (X := X) (0 : k) _)
    (pullbackSectionAtBiproductIso (X := X) (0 : k) _)
    ((Iso.inv_comp_eq _).1 (pullbackSectionAtBiproductIso_inv_comp_map_syzygy S j))

theorem kernel_ι_comp_factorThruImage_gen (j : ℕ) :
    CategoryTheory.Limits.kernel.ι (gen S j) ≫ CategoryTheory.Limits.factorThruImage (gen S j) = 0 := by
  rw [← cancel_mono (CategoryTheory.Limits.image.ι (gen S j)), Category.assoc, CategoryTheory.Limits.image.fac,
    CategoryTheory.Limits.kernel.condition, zero_comp]

/-- `kernel (gen S j)` is also a kernel of `factorThruImage (gen S j)` (the image inclusion is mono). -/
noncomputable def kernelForkFactorThruImageGenIsLimit (j : ℕ) :
    CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.KernelFork.ofι (CategoryTheory.Limits.kernel.ι (gen S j))
      (kernel_ι_comp_factorThruImage_gen S j)) :=
  CategoryTheory.Limits.KernelFork.IsLimit.ofι _ _
    (fun g' hg' => CategoryTheory.Limits.kernel.lift (gen S j) g'
      (by rw [← CategoryTheory.Limits.image.fac (gen S j), ← Category.assoc, hg', zero_comp]))
    (fun g' hg' => CategoryTheory.Limits.kernel.lift_ι _ _ _)
    (fun g' hg' m hm => by rw [← cancel_mono (CategoryTheory.Limits.kernel.ι (gen S j)),
      CategoryTheory.Limits.kernel.lift_ι, hm])

/-- `factorThruImage (gen S j) : ⊕_e π^*I^{(j-e)}_j → R_j` is the cokernel of `kernel.ι (gen S j)`
(an epimorphism in an abelian category is the cokernel of its kernel). -/
noncomputable def factorThruImageGenIsColimit (j : ℕ) :
    CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ
      (CategoryTheory.Limits.factorThruImage (gen S j)) (kernel_ι_comp_factorThruImage_gen S j)) :=
  CategoryTheory.Abelian.epiIsCokernelOfKernel _ (kernelForkFactorThruImageGenIsLimit S j)

/-- `s₀^*` preserves it: `s₀^*(factorThruImage (gen S j))` is the cokernel of `s₀^*(kernel.ι (gen S j))`. -/
noncomputable def pullbackSectionAtZeroFactorThruImageGenIsColimit (j : ℕ) :
    CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ
      ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (CategoryTheory.Limits.factorThruImage (gen S j)))
      (by
        have := pullbackSectionAt_additive (X := X) (0 : k)
        rw [← Functor.map_comp, kernel_ι_comp_factorThruImage_gen, Functor.map_zero]) :
      CategoryTheory.Limits.CokernelCofork
        ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (CategoryTheory.Limits.kernel.ι (gen S j)))) :=
  haveI : PreservesColimitsOfSize.{0, 0} (Modules.pullback (affineLineOver.sectionAt X (0 : k))) :=
    (Modules.pullbackPushforwardAdjunction _).leftAdjoint_preservesColimits
  CategoryTheory.Limits.isColimitCoforkMapOfIsColimit' _ _ (factorThruImageGenIsColimit S j)

/-- `s₀^*R_j ≅ coker (s₀^*(ker gen) → s₀^*(⊕ π^*I))`. -/
noncomputable def pullbackSectionAtZeroPartIsoCokernel (j : ℕ) :
    (Modules.pullback (affineLineOver.sectionAt X (0 : k))).obj (CategoryTheory.Limits.image (gen S j)) ≅
      CategoryTheory.Limits.cokernel
        ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (CategoryTheory.Limits.kernel.ι (gen S j))) :=
  (pullbackSectionAtZeroFactorThruImageGenIsColimit S j).coconePointUniqueUpToIso
    (CategoryTheory.Limits.colimit.isColimit _)

theorem map_factorThruImage_gen_comp_pullbackSectionAtZeroPartIsoCokernel_hom (j : ℕ) :
    (Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (CategoryTheory.Limits.factorThruImage (gen S j)) ≫
        (pullbackSectionAtZeroPartIsoCokernel S j).hom =
      CategoryTheory.Limits.cokernel.π _ :=
  CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
    (pullbackSectionAtZeroFactorThruImageGenIsColimit S j) (CategoryTheory.Limits.colimit.isColimit _)
    CategoryTheory.Limits.WalkingParallelPair.one

/-- `s₀^*ψ_j` dies in `coker (s₀^*(ker gen))`: `ψ_j` factors through `ker gen` (`syzygy_comp_gen`). -/
theorem map_syzygy_comp_cokernel_π_map_kernel_ι (j : ℕ) :
    (Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (syzygy S j) ≫
      CategoryTheory.Limits.cokernel.π
        ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (CategoryTheory.Limits.kernel.ι (gen S j))) = 0 := by
  rw [← CategoryTheory.Limits.kernel.lift_ι (gen S j) (syzygy S j) (syzygy_comp_gen S j), Functor.map_comp,
    Category.assoc, CategoryTheory.Limits.cokernel.condition, comp_zero]

/-- **The local content: `s₀^*(ker gen) → ⊕_e I^{(j-e)}_j` dies in `coker (s₀^*ψ_j)`.** Source: Stacks 052P
("`R/λR = gr_I(A)`" for the extended Rees algebra).

Proof from the exactness of the syzygy sequence, `ker (gen S j) = Im ψ_j`
(`reesDeformation.exact_syzygy_gen` / `epi_kernel_lift_syzygy` in `DeformedJetAlgebraSyzygy`), which needs no
affine cover: the lift `ψ'_j : ⊕_e π^*I^{(j-e+1)}_j → ker gen` is an epimorphism, `s₀^*` (a left adjoint) preserves
epimorphisms, and `s₀^*ψ'_j ≫ s₀^*(kernel.ι) ≫ cokernel.π (s₀^*ψ_j) = s₀^*ψ_j ≫ cokernel.π (s₀^*ψ_j) = 0`; cancel the
epimorphism. The local inputs are the two lemmas of `AffineLinePullbackTorsionFree`: `λ` is a nonzerodivisor on
`π^*N` and `π^*` preserves monomorphisms (`π : A¹_X → X` is flat), both for quasi-coherent `N`. -/
theorem map_kernel_ι_comp_cokernel_π_map_syzygy (j : ℕ) :
    (Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (CategoryTheory.Limits.kernel.ι (gen S j)) ≫
      CategoryTheory.Limits.cokernel.π
        ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (syzygy S j)) = 0 := by
  haveI : (Modules.pullback (affineLineOver.sectionAt X (0 : k))).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Modules.pullbackPushforwardAdjunction _)
  haveI := epi_kernel_lift_syzygy S j
  haveI : Epi ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map
      (CategoryTheory.Limits.kernel.lift (gen S j) (syzygy S j) (syzygy_comp_gen S j))) :=
    Functor.map_epi _ _
  rw [← cancel_epi ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map
      (CategoryTheory.Limits.kernel.lift (gen S j) (syzygy S j) (syzygy_comp_gen S j))),
    ← Category.assoc, ← Functor.map_comp, CategoryTheory.Limits.kernel.lift_ι,
    CategoryTheory.Limits.cokernel.condition, comp_zero]

/-- `coker (s₀^*ψ_j) ≅ coker (s₀^*(ker gen))` (both are quotients of `s₀^*(⊕ π^*I)`, each factoring through the other:
`isoOfEpiFactor`). -/
noncomputable def cokernelMapSyzygyIsoCokernelMapKernelι (j : ℕ) :
    CategoryTheory.Limits.cokernel ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (syzygy S j)) ≅
      CategoryTheory.Limits.cokernel
        ((Modules.pullback (affineLineOver.sectionAt X (0 : k))).map (CategoryTheory.Limits.kernel.ι (gen S j))) :=
  CategoryTheory.Limits.isoOfEpiFactor (CategoryTheory.Limits.cokernel.π _) (CategoryTheory.Limits.cokernel.π _)
    (CategoryTheory.Limits.cokernel.desc _ _ (map_syzygy_comp_cokernel_π_map_kernel_ι S j))
    (CategoryTheory.Limits.cokernel.desc _ _ (map_kernel_ι_comp_cokernel_π_map_syzygy S j))
    (CategoryTheory.Limits.cokernel.π_desc _ _ _) (CategoryTheory.Limits.cokernel.π_desc _ _ _)

/-- Reindexing `e ↦ p = j - e` (`Fin.revPerm`): `⊕_e coker (stepHom (j-e) j) ≅ ⊕_p coker (stepHom p j)`. -/
noncomputable def biproductCokernelStepHomReindexIso (j : ℕ) :
    (⨁ fun e : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S (j - e.1) j)) ≅
      ⨁ fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j) :=
  (CategoryTheory.Limits.biproduct.mapIso (fun e : Fin (j + 1) =>
      eqToIso (congrArg (fun m => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S m j))
        (show j - e.1 = (Fin.rev e).1 by rw [Fin.val_rev]; omega))) :
    (⨁ fun e : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S (j - e.1) j)) ≅
      ⨁ ((fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) ∘ Fin.revPerm)) ≪≫
    CategoryTheory.Limits.biproduct.reindex Fin.revPerm
      (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j))

end reesDeformation

/-! ## §2 Leaves -/

namespace reesDeformation

variable {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- **The isomorphism as a named `def`**: `(s₀^*R)_j ≅ ⊕_{p ≤ j} coker (stepHom S p j) = ⊕_p I^{(p)}_j/I^{(p+1)}_j`,
the composite of §1c and §0a (see `reesDeformation_restrictToLambda_zero_part_iso`, whose proof is `⟨partIsoGr S j⟩`).
Kept as data so that the algebra-level statement can use the explicit maps (the `p`-th summand inclusion into the
fibre, the multiplicativity of the identification). -/
noncomputable def partIsoGr (j : ℕ) :
    (S.reesDeformation.restrictToLambda (0 : k)).part j ≅
      ⨁ (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j)) :=
  pullbackSectionAtZeroPartIsoCokernel S j ≪≫
    (cokernelMapSyzygyIsoCokernelMapKernelι S j).symm ≪≫
    cokernelPullbackSyzygyIso S j ≪≫
    CategoryTheory.Limits.cokernelBiproductMapIso _ ≪≫
    biproductCokernelStepHomReindexIso S j

end reesDeformation

/-- **The fibre at `λ = 0` of a Rees piece is the associated graded piece** (generic `S`; source: Stacks 052P
"`R/λR = gr_I(A)`" for the extended Rees algebra).

Proof (categorical). Write `F := s₀^*`, `π^*` for the pullback along
`toBase X`, `R_j = Im (gen S j)`, `gen S j : ⊕_{e≤j} π^*I^{(j-e)}_j → π^*S_j` (`e`-th component `λ^e·π^*incl`).
(1) `F(R_j) = coker (F(ker gen) → F(⊕ π^*I))`: `factorThruImage gen` is an epimorphism, hence the cokernel of its kernel
(`Abelian.epiIsCokernelOfKernel`), and the left adjoint `F` preserves cokernels (`pullbackSectionAtZeroPartIsoCokernel`).
(2) The syzygy `ψ_j` (§1b) satisfies `ψ_j ≫ gen = 0`, so `F ψ_j` dies in `coker F(ker gen)`; conversely `F(ker gen)` dies in
`coker (F ψ_j)` (`map_kernel_ι_comp_cokernel_π_map_syzygy`), so the two cokernels of `F(⊕ π^*I)` coincide (`isoOfEpiFactor`,
`cokernelMapSyzygyIsoCokernelMapKernelι`). (3) `F ∘ π^* ≅ 𝟭` and `F` is additive, so `F(⊕ π^*M_e) ≅ ⊕ M_e`
(`pullbackSectionAtBiproductIso`); the `λ`-terms of `ψ_j` die along `λ = 0` (§0), so `F ψ_j = ⊕_e stepHom (j-e) j`
(`pullbackSectionAtBiproductIso_inv_comp_map_syzygy`, `cokernelPullbackSyzygyIso`). (4) `coker (⊕ f_e) = ⊕ coker f_e`
(`cokernelBiproductMapIso`) and reindex `e ↦ p = j - e` (`biproductCokernelStepHomReindexIso`); the `e = 0` summand
`coker (stepHom j j) = I^{(j)}_j` because `I^{(j+1)}_j = 0` (§1a). Edge cases: `j = 0`: `R_0 = π^*S_0`, `ψ_0 = 0`, both sides `S_0`;
`X = ∅`: both sides `0`. -/
theorem reesDeformation_restrictToLambda_zero_part_iso {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (S : X.GradedQCAlgebra) (j : ℕ) :
    Nonempty ((S.reesDeformation.restrictToLambda (0 : k)).part j ≅
      ⨁ (fun p : Fin (j + 1) => CategoryTheory.Limits.cokernel (irrelevantPow.stepHom S p.1 j))) :=
  ⟨reesDeformation.partIsoGr S j⟩

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
