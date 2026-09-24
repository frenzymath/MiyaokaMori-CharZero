import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualCurry
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualMapFunctorial
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameRankOne
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionConstructions
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceTriangleTransport
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.TotalSpaceLinearCoordinate
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquivCoordinateDualFrame
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquivCoordinateFunctional

/-! # The coordinates of `totalSpaceHomEquiv` in a frame (helper of `JetWeightComponentEqCoefficient`)

This is step (4) of the docstring of `BasedJet.exists_pieceSection_generatesAt`: "`totalSpaceHomEquiv` in a frame
is `J^♯ x_ℓ^a · (p ≫ ρ)^*a`". Everything here is stated at the variable level (`X` a scheme, `V A : X.Modules`,
`T : Over X`).

Setting: `Tot(V) = Spec_X Sym(V^∨)`; an `X`-morphism `h : T → Tot(V)` corresponds to
the section `z := totalSpaceHomEquiv V T h ∈ Γ(T, g^*V)` (`g := T.hom`), and to the functional
`ψ_z := functionalOfSection V T z : g^*(V^∨) → O_T` (`TotalSpaceSectionEquiv.lean`).

* `functionalOfSection_totalSpaceHomEquiv`: `ψ_z = functionalOfHomCore V T h`, the degree-one part of the algebra
  map `Sym(V^∨) → g_*O_T` of `h`, transposed (triangle identity `functionalOfSectionCore_sectionOfFunctionalCore`).
* `functionalOfHomCore_app_unit`: on the unit section `η(t)` of `t ∈ Γ(V^∨, U)`, that functional is
  `h^♯(linearFunction V U t)`, the pullback along `h` of the linear function of `t` on `Tot(V)`
  (`TotalSpaceLinearCoordinate.lean`); unfolding `relativeSpec.toAlgebraMap` (`pullbackSections`) and
  `structureHom_app_apply`.
* `functionalOfSection_pullback_map`: naturality in `V`: for `φ : V ⟶ A`,
  `ψ_{g^*φ(z)} = g^*(φ^∨) ≫ ψ_z` (the defining property `(φ^∨ ▷ V) ≫ ev_V = (A^∨ ◁ φ) ≫ ev_A` of `dualMap`,
  `dualCurry_symm_apply`, and the naturality of the oplax structure `δ` of `g^*`).
* **`totalSpaceHomEquiv_coordinate_res_eq_smul`** (the statement used downstream): for `V = A^{⊕n}`, a frame `a` of `A`
  on `U ⊆ X` with dual frame `α = a^∨` (`IsFrame.dualSec`), and `ℓ : Fin n`, the `ℓ`-th coordinate
  `z_ℓ := g^*(π_ℓ)(z) ∈ Γ(T, g^*A)` restricted to `g⁻¹U` is
  `h^♯(x_ℓ^α) • η(a)`, where `x_ℓ^α = coordinateFunction A n ℓ U α ∈ Γ(Tot(A^{⊕n}), π⁻¹U)` is the `ℓ`-th linear
  coordinate function of the frame. Proof: `η(a)` is a frame of `g^*A` on `g⁻¹U` (`isFrame_unitSec_pullback`), so
  `z_ℓ|_{g⁻¹U} = c • η(a)` with `c` its coordinate; `ψ_{z_ℓ}(η(α)) = c` because `⟨α, a⟩ = 1`
  (`functionalOfSection_app_unit_of_res_eq_smul`, `IsFrame.dualEv_dualSec_frame`); and
  `ψ_{z_ℓ}(η(α)) = ψ_z(η(π_ℓ^∨ α)) = h^♯(linearFunction (π_ℓ^∨ α)) = h^♯(x_ℓ^α)` by the three lemmas above.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace CategoryTheory.Functor.OplaxMonoidal

variable {C : Type*} {D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

/-- **Abstract naturality of the functional of a section.** `F : D ⥤ C` oplax monoidal (with `δ` natural),
`φ : V ⟶ A`, a "dual map" `dm : A' ⟶ V'` and pairings `evV`, `evA` with `(dm ▷ V) ≫ evV = (A' ◁ φ) ≫ evA`;
`s : 𝟙 ⟶ F V` a "section", `u : F 𝟙 ⟶ 𝟙`; `eV, eA, eAV` the comparison isomorphisms whose `hom` is `δ`. Then
`ρ⁻¹ ≫ (F A' ◁ (s ≫ F φ)) ≫ eA⁻¹ ≫ F evA ≫ u = F dm ≫ ρ⁻¹ ≫ (F V' ◁ s) ≫ eV⁻¹ ≫ F evV ≫ u`.
(Pure monoidal rewriting; stated abstractly so that every instance is a variable.) -/
theorem functional_naturality_aux (F : D ⥤ C) [inst : F.OplaxMonoidal] {V A V' A' : D} (φ : V ⟶ A) (dm : A' ⟶ V')
    (evV : V' ⊗ V ⟶ 𝟙_ D) (evA : A' ⊗ A ⟶ 𝟙_ D) (hdual : (dm ▷ V) ≫ evV = (A' ◁ φ) ≫ evA)
    (eV : F.obj (V' ⊗ V) ≅ F.obj V' ⊗ F.obj V) (heV : eV.hom = δ F V' V)
    (eA : F.obj (A' ⊗ A) ≅ F.obj A' ⊗ F.obj A) (heA : eA.hom = δ F A' A)
    (eAV : F.obj (A' ⊗ V) ≅ F.obj A' ⊗ F.obj V) (heAV : eAV.hom = δ F A' V)
    (s : 𝟙_ C ⟶ F.obj V) (s' : 𝟙_ C ⟶ F.obj A) (hs' : s' = s ≫ F.map φ) (u : F.obj (𝟙_ D) ⟶ 𝟙_ C) :
    (ρ_ (F.obj A')).inv ≫ (F.obj A' ◁ s') ≫ eA.inv ≫ F.map evA ≫ u =
      F.map dm ≫ (ρ_ (F.obj V')).inv ≫ (F.obj V' ◁ s) ≫ eV.inv ≫ F.map evV ≫ u := by
  subst hs'
  have n1 : (F.map dm ▷ F.obj V) ≫ eV.inv = eAV.inv ≫ F.map (dm ▷ V) := by
    rw [Iso.comp_inv_eq, Category.assoc, heV, Iso.eq_inv_comp, heAV]
    exact δ_natural_left F dm V
  have n2 : (F.obj A' ◁ F.map φ) ≫ eA.inv = eAV.inv ≫ F.map (A' ◁ φ) := by
    rw [Iso.comp_inv_eq, Category.assoc, heA, Iso.eq_inv_comp, heAV]
    exact δ_natural_right F A' φ
  rw [MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.rightUnitor_inv_naturality_assoc,
    ← MonoidalCategory.whisker_exchange_assoc, reassoc_of% n1, ← Functor.map_comp_assoc, hdual,
    Functor.map_comp_assoc, ← reassoc_of% n2]

end CategoryTheory.Functor.OplaxMonoidal

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- The defining property of `dualMap`: `(φ^∨ ▷ V) ≫ ev_V = (A^∨ ◁ φ) ≫ ev_A`. -/
theorem dualMap_whiskerRight_dualEv {V A : X.Modules} (φ : V ⟶ A) :
    (dualMap φ ▷ V) ≫ dualEv V = (dual A ◁ φ) ≫ dualEv A := by
  rw [dualMap_eq, ← dualCurry_symm_apply, Equiv.symm_apply_apply]

/-- Naturality of `δ⁻¹ : g^*M ⊗ g^*N ≅ g^*(M ⊗ N)` in the left variable. -/
@[reassoc]
theorem pullbackTensorObjIso_inv_natural_left (g : T ⟶ X) {M M' : X.Modules} (f : M ⟶ M') (N : X.Modules) :
    ((pullback g).map f ▷ (pullback g).obj N) ≫ (pullbackTensorObjIso g M' N).inv =
      (pullbackTensorObjIso g M N).inv ≫ (pullback g).map (f ▷ N) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact Functor.OplaxMonoidal.δ_natural_left (F := pullback g) (self := pullbackOplaxMonoidal g) f N

/-- Naturality of `δ⁻¹ : g^*M ⊗ g^*N ≅ g^*(M ⊗ N)` in the right variable. -/
@[reassoc]
theorem pullbackTensorObjIso_inv_natural_right (g : T ⟶ X) (M : X.Modules) {N N' : X.Modules} (f : N ⟶ N') :
    ((pullback g).obj M ◁ (pullback g).map f) ≫ (pullbackTensorObjIso g M N').inv =
      (pullbackTensorObjIso g M N).inv ≫ (pullback g).map (M ◁ f) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact Functor.OplaxMonoidal.δ_natural_right (F := pullback g) (self := pullbackOplaxMonoidal g) M f

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.totalSpace

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `ψ_{totalSpaceHomEquiv h} = functionalOfHomCore h` (definitional unfolding plus the triangle identity
`functionalOfSectionCore_sectionOfFunctionalCore`). -/
theorem functionalOfSection_totalSpaceHomEquiv (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    AlgebraicGeometry.Scheme.totalSpace.functionalOfSection V T
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T h) =
      AlgebraicGeometry.Scheme.totalSpace.functionalOfHomCore V T h := by
  change AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T
    (AlgebraicGeometry.Scheme.totalSpace.sectionOfFunctionalCore V T
      (AlgebraicGeometry.Scheme.totalSpace.functionalOfHomCore V T h)) = _
  exact AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore_sectionOfFunctionalCore V T _

/-- `T.hom⁻¹U ≤ h.left⁻¹(π⁻¹U)` for an `X`-morphism `h : T ⟶ Tot(V)`. -/
theorem preimage_le_of_over (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) (U : X.Opens) :
    T.hom ⁻¹ᵁ U ≤ h.left ⁻¹ᵁ ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U) := by
  rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, CategoryTheory.Over.w]

/-- On the unit section `η(t)` (`t ∈ Γ(V^∨, U)`), `functionalOfHomCore h` is `h^♯(linearFunction V U t)`. -/
theorem functionalOfHomCore_app_unit (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) (U : X.Opens)
    (t : Γ(AlgebraicGeometry.Scheme.Modules.dual V, U)) :
    (AlgebraicGeometry.Scheme.totalSpace.functionalOfHomCore V T h).app (T.hom ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).unit.app
          (AlgebraicGeometry.Scheme.Modules.dual V)).app U t) =
      h.left.appLE ((AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U) (T.hom ⁻¹ᵁ U)
        (preimage_le_of_over V T h U) (AlgebraicGeometry.Scheme.totalSpace.linearFunction V U t) := by
  have h1 := AlgebraicGeometry.Scheme.Modules.homEquiv_symm_app_unit T.hom
    (AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
      CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).part 1 ≫
      AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total T h)
    U t
  refine h1.trans ?_
  have e2 : AlgebraicGeometry.Scheme.totalSpace.linearFunction V U t =
      (AlgebraicGeometry.Scheme.relativeSpec.structureHom
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total).app U
        ((CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).part 1).app U
          ((AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V)).app U t)) := rfl
  have e3 : AlgebraicGeometry.Scheme.totalSpace.linearFunction V U t =
      ((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total).app
          (Opposite.op U)).hom
        ((CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).part 1).app U
          ((AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V)).app U t)) :=
    e2.trans (AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_apply _ _ _)
  rw [e3]
  rfl

/-- Naturality of `functionalOfSection` in the module: `ψ_{g^*φ(z)} = g^*(φ^∨) ≫ ψ_z`. -/
theorem functionalOfSection_pullback_map (V A : X.Modules) (φ : V ⟶ A) (T : CategoryTheory.Over X)
    (z : Γ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V, ⊤)) :
    AlgebraicGeometry.Scheme.totalSpace.functionalOfSection A T
        (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map φ).app ⊤ z) =
      (AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (AlgebraicGeometry.Scheme.Modules.dualMap φ) ≫
        AlgebraicGeometry.Scheme.totalSpace.functionalOfSection V T z := by
  unfold AlgebraicGeometry.Scheme.totalSpace.functionalOfSection
  exact CategoryTheory.Functor.OplaxMonoidal.functional_naturality_aux
    (AlgebraicGeometry.Scheme.Modules.pullback T.hom) (inst := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal T.hom)
    φ (AlgebraicGeometry.Scheme.Modules.dualMap φ) (AlgebraicGeometry.Scheme.Modules.dualEv V)
    (AlgebraicGeometry.Scheme.Modules.dualEv A) (AlgebraicGeometry.Scheme.Modules.dualMap_whiskerRight_dualEv φ)
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso T.hom (AlgebraicGeometry.Scheme.Modules.dual V) V) rfl
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso T.hom (AlgebraicGeometry.Scheme.Modules.dual A) A) rfl
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso T.hom (AlgebraicGeometry.Scheme.Modules.dual A) V) rfl
    (AlgebraicGeometry.Scheme.Modules.homOfTopSection _ z)
    (AlgebraicGeometry.Scheme.Modules.homOfTopSection _
      (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map φ).app ⊤ z))
    (AlgebraicGeometry.Scheme.Modules.DualZigzag.homOfTopSection_app_top
      ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map φ) z)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso T.hom).hom

/-- **The `ℓ`-th coordinate of `totalSpaceHomEquiv` in a frame.** For `V = A^{⊕n}`, an `X`-morphism
`h : T ⟶ Tot(A^{⊕n})` with `z := totalSpaceHomEquiv h ∈ Γ(T, g^*A^{⊕n})` (`g = T.hom`), a frame `a` of `A` on `U`
with dual frame `α := a^∨`, the coordinate `z_ℓ := g^*(π_ℓ)(z)` restricted to `g⁻¹U` equals
`h^♯(x_ℓ^α) • η(a)`, `x_ℓ^α := coordinateFunction A n ℓ U α`. -/
theorem totalSpaceHomEquiv_coordinate_res_eq_smul (A : X.Modules) [A.IsLocallyFree] [A.IsFiniteType] (n : ℕ)
    (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n))
    (ℓ : Fin n) (U : X.Opens) {a : Γ(A, U)} (hf : AlgebraicGeometry.Scheme.Modules.IsFrame A U a) :
    ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj A).res (le_top : T.hom ⁻¹ᵁ U ≤ ⊤)
        (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map
          (CategoryTheory.Limits.biproduct.π (fun _ : Fin n => A) ℓ : AlgebraicGeometry.Scheme.Modules.pow A n ⟶ A)).app ⊤
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A n) T h)) =
      h.left.appLE ((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom ⁻¹ᵁ U)
          (T.hom ⁻¹ᵁ U) (preimage_le_of_over (AlgebraicGeometry.Scheme.Modules.pow A n) T h U)
          (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction A n ℓ U hf.dualSec) •
        (show Γ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj A, T.hom ⁻¹ᵁ U) from
          ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).unit.app A).app U a) := by
  set zℓ : Γ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj A, ⊤) :=
    ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin n => A) ℓ : AlgebraicGeometry.Scheme.Modules.pow A n ⟶ A)).app ⊤
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A n) T h) with hzℓ
  have hfr : AlgebraicGeometry.Scheme.Modules.IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj A)
      (T.hom ⁻¹ᵁ U) (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).unit.app A).app U a) :=
    MiyaokaMori.DualPullback.isFrame_unitSec_pullback T.hom A hf
  set c : Γ(T.left, T.hom ⁻¹ᵁ U) :=
    hfr.coord le_rfl (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj A).res (le_top : T.hom ⁻¹ᵁ U ≤ ⊤) zℓ)
    with hc
  have hs : ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj A).res (le_top : T.hom ⁻¹ᵁ U ≤ ⊤) zℓ =
      c • (show Γ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj A, T.hom ⁻¹ᵁ U) from
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).unit.app A).app U a) := by
    have := hfr.coord_smul_frame le_rfl
      (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj A).res (le_top : T.hom ⁻¹ᵁ U ≤ ⊤) zℓ)
    refine this.symm.trans (congrArg (fun y => c • y) ?_)
    exact AlgebraicGeometry.Scheme.Modules.res_self ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj A) _
  have h1 := AlgebraicGeometry.Scheme.totalSpace.functionalOfSection_app_unit_of_res_eq_smul A T zℓ U hf.dualSec a
    hf.dualEv_dualSec_frame c hs
  have h2 : (AlgebraicGeometry.Scheme.totalSpace.functionalOfSection A T zℓ).app (T.hom ⁻¹ᵁ U)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).unit.app
        (AlgebraicGeometry.Scheme.Modules.dual A)).app U hf.dualSec) =
      h.left.appLE ((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom ⁻¹ᵁ U)
        (T.hom ⁻¹ᵁ U) (preimage_le_of_over (AlgebraicGeometry.Scheme.Modules.pow A n) T h U)
        (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction A n ℓ U hf.dualSec) := by
    have e := functionalOfSection_pullback_map (AlgebraicGeometry.Scheme.Modules.pow A n) A
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin n => A) ℓ : AlgebraicGeometry.Scheme.Modules.pow A n ⟶ A) T
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A n) T h)
    have e' := congrArg (fun ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual A) ⟶ SheafOfModules.unit T.left.ringCatSheaf =>
      ψ.app (T.hom ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).unit.app
          (AlgebraicGeometry.Scheme.Modules.dual A)).app U hf.dualSec)) e
    refine e'.trans ?_
    have h4 := AlgebraicGeometry.Scheme.Modules.pullback_map_app_unit T.hom
      (AlgebraicGeometry.Scheme.Modules.dualMap
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin n => A) ℓ : AlgebraicGeometry.Scheme.Modules.pow A n ⟶ A))
      U hf.dualSec
    have h5 := functionalOfSection_totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A n) T h
    have h6 := functionalOfHomCore_app_unit (AlgebraicGeometry.Scheme.Modules.pow A n) T h U
      ((AlgebraicGeometry.Scheme.Modules.dualMap
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin n => A) ℓ : AlgebraicGeometry.Scheme.Modules.pow A n ⟶ A)).app U
        hf.dualSec)
    refine Eq.trans ?_ h6
    rw [← h5]
    exact congrArg (fun y => (AlgebraicGeometry.Scheme.totalSpace.functionalOfSection
      (AlgebraicGeometry.Scheme.Modules.pow A n) T
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A n) T h)).app (T.hom ⁻¹ᵁ U) y) h4
  rw [hs, ← h1, h2]

end AlgebraicGeometry.Scheme.totalSpace

end
