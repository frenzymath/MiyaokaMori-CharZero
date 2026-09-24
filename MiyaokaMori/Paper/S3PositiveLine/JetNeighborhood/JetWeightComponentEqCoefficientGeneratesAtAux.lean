import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedLineBundleIsLineBundle
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetConeCoordinate
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.NormalizedTupleNowhereZero
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.SectionIsZeroAtIso
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineMonomialZeroSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.TotalSpaceLinearCoordinate
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficientFrameCoordinate
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficientProjectionFormulaLocal
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficientGermCriteria

/-! # Existence of a generating piece section, concrete part (helper of `JetWeightComponentEqCoefficient`)

This module proves the coefficient formula of step (4) of the docstring of
`BasedJet.exists_pieceSection_generatesAt` for the concrete data of the paper, and derives from it the
"generates at `y`" statement in unfolded form (`BasedJet.exists_pieceSection_germ_notMem_of_not_isZeroAt`);
the main module only repackages it with `pieceSection`/`GeneratesAt` (both defined there).

Notation: `A := seedLineBundle X.embedding f = f^*O(1)` on `C`, `V := A^{⊕(N+1)}`, `p : C̃_(κ)(L) → C̃`,
`T := (p ≫ ρ : C̃_(κ)(L) → C)`, `coneι : 𝒵 ↪ Tot(V)`, `θ' := f^*(eqToHom) : A ⟶ (f^*O_X(1)).toModules`,
`M := ρ^*f^*O(1)` (a line bundle on `C̃`), `W := ρ⁻¹U`.

* `coneCoordinate_eq` (`rfl`): `coneCoordinate J ℓ = p^*ρ^*θ'((pullbackComp p ρ)⁻¹(π_ℓ(totalSpaceHomEquiv (J ≫ coneι))))`.
* `coneCoordinate_res_eq_smul`: for a frame `a` of `A` on `U`, on `p⁻¹W`:
  `coneCoordinate J ℓ = c • η_p(η_ρ(θ' a))`, `c := (J ≫ coneι)^♯(x_ℓ^{a^∨})` (`…FrameCoordinate.lean` +
  `pullbackComp_inv_app_unit` + `pullback_map_app_unit`).
* `pullbackSectionToPushforward_coneCoordinate_res`: hence `(pullbackSectionToPushforward p M (coneCoordinate J ℓ))|_W
  = a_M ⊗ c` with `a_M := η_ρ(θ' a)` a frame of `M` on `W` (`…ProjectionFormulaLocal.lean`).
* `coefficient_eq`: `J.coefficient ℓ m = ((M ◁ χ_m) ≫ Φ')(pullbackSectionToPushforward p M (coneCoordinate J ℓ))`
  for `m ≤ κ` (`dif_pos`), `χ_m := structureIso⁻¹ ≫ π_m ≫ pieceIso ≫ monoidalPowIsoTensorPower`,
  `Φ' := tensorIsoTensorObj⁻¹ ≫ coefficientModuleIso`.
* `exists_pieceSection_germ_notMem_of_not_isZeroAt`: if `coefficient ℓ m` does not vanish at `y`, then for
  `U ∋ ρ(y)` affine with a frame `a` (`exists_affine_frame_le`) and `b := x_ℓ^{a^∨}|_𝒵 ∈ Γ(𝒵, π⁻¹U)`
  (`coordinateFunctionOn`), the germ at `y` of `(structureIso⁻¹ ≫ π_m ≫ pieceIso)(J^♯ b)` (this is
  `J.pieceSection U m _ b`) is not in `𝔪_y • ⊤`. Contrapositive chain: `(J ≫ coneι)^♯ x = J^♯(coneι^♯ x)`
  (`appLE_comp_appLE`), `χ_m(c) = monoidalPowIsoTensorPower(pieceSection)`, then the germ criteria of
  `…GermCriteria.lean` (isomorphism, tensor with the frame `a_M` on the left, restriction to `W`), and
  `isZeroAt_hom_app` for `Φ'`.

Source: proof of Lemma 3.1 of the paper (the coefficients `c_{ℓ,q}` are read off in a
frame `ε`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {S Y Z : AlgebraicGeometry.Scheme.{u}}

/-- **Transport of "`z|_{(p≫ρ)⁻¹U} = c • η(a)`" through `(pullbackComp p ρ)⁻¹` and `p^*ρ^*θ`** (variable level):
the result restricted to `p⁻¹ρ⁻¹U` is `c • η_p(η_ρ(θ a))`. -/
theorem res_pullback_map_pullbackComp_inv_of_res_eq_smul (p : S ⟶ Y) (ρ : Y ⟶ Z) {A A' : Z.Modules} (θ : A ⟶ A')
    (U : Z.Opens) (a : Γ(A, U)) (z : Γ((pullback (p ≫ ρ)).obj A, ⊤)) (c : Γ(S, p ⁻¹ᵁ (ρ ⁻¹ᵁ U)))
    (hz : ((pullback (p ≫ ρ)).obj A).res (le_top : (p ≫ ρ) ⁻¹ᵁ U ≤ ⊤) z =
      (show Γ(S, (p ≫ ρ) ⁻¹ᵁ U) from c) • (show Γ((pullback (p ≫ ρ)).obj A, (p ≫ ρ) ⁻¹ᵁ U) from
        ((pullbackPushforwardAdjunction (p ≫ ρ)).unit.app A).app U a)) :
    ((pullback p).obj ((pullback ρ).obj A')).res (le_top : p ⁻¹ᵁ (ρ ⁻¹ᵁ U) ≤ ⊤)
        (((pullback p).map ((pullback ρ).map θ)).app ⊤ (((pullbackComp p ρ).inv.app A).app ⊤ z)) =
      c • (show Γ((pullback p).obj ((pullback ρ).obj A'), p ⁻¹ᵁ (ρ ⁻¹ᵁ U)) from
        ((pullbackPushforwardAdjunction p).unit.app ((pullback ρ).obj A')).app (ρ ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction ρ).unit.app A').app U (θ.app U a))) := by
  have s2 := Hom.app_res ((pullbackComp p ρ).inv.app A) (le_top : (p ≫ ρ) ⁻¹ᵁ U ≤ ⊤) z
  have s3 := pullbackComp_inv_app_unit p ρ A U a
  have s4 := Hom.app_res ((pullback p).map ((pullback ρ).map θ)) (le_top : p ⁻¹ᵁ (ρ ⁻¹ᵁ U) ≤ ⊤)
    (((pullbackComp p ρ).inv.app A).app ⊤ z)
  have s5 := pullback_map_app_unit p ((pullback ρ).map θ) (ρ ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction ρ).unit.app A).app U a)
  have s6 := pullback_map_app_unit ρ θ U a
  refine s4.symm.trans ?_
  have s7 : ((pullback p).obj ((pullback ρ).obj A)).res (le_top : p ⁻¹ᵁ (ρ ⁻¹ᵁ U) ≤ ⊤)
      (((pullbackComp p ρ).inv.app A).app ⊤ z) =
      c • (show Γ((pullback p).obj ((pullback ρ).obj A), p ⁻¹ᵁ (ρ ⁻¹ᵁ U)) from
        ((pullbackPushforwardAdjunction p).unit.app ((pullback ρ).obj A)).app (ρ ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction ρ).unit.app A).app U a)) := by
    refine s2.symm.trans ?_
    rw [hz, Hom.app_smul]
    exact congrArg (fun w : Γ((pullback p).obj ((pullback ρ).obj A), p ⁻¹ᵁ (ρ ⁻¹ᵁ U)) => c • w) s3
  rw [s7, Hom.app_smul, s5, s6]

/-- **Germ criterion through `M ◁ χ` on a section that is `a ⊗ t` on `W`** (variable level): if `a` is a frame of
`M` on `W` and `Q|_W = a ⊗ t`, then `((M ◁ χ) Q)_y ∈ 𝔪_y • ⊤ ↔ (χ t)_y ∈ 𝔪_y • ⊤`. -/
theorem germ_whiskerLeft_app_mem_maximalIdeal_smul_iff_of_res_eq_tensorSections {M N N' : Y.Modules} (χ : N ⟶ N')
    (Q : Γ(M ⊗ N, ⊤)) {W : Y.Opens} {y : Y} (hy : y ∈ W) {a : Γ(M, W)} (hf : IsFrame M W a) (t : Γ(N, W))
    (hQ : (M ⊗ N).res (le_top : W ≤ ⊤) Q = tensorSections M N W a t) :
    (M ⊗ N').presheaf.germ ⊤ y trivial ((M ◁ χ).app ⊤ Q) ∈
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) •
          (⊤ : Submodule (Y.presheaf.stalk y) ((M ⊗ N').presheaf.stalk y)) ↔
      N'.presheaf.germ W y hy (χ.app W t) ∈
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) •
          (⊤ : Submodule (Y.presheaf.stalk y) (N'.presheaf.stalk y)) := by
  have e1 : (M ⊗ N').res (le_top : W ≤ ⊤) ((M ◁ χ).app ⊤ Q) = tensorSections M N' W a (χ.app W t) := by
    rw [← Hom.app_res, hQ]
    exact whiskerLeft_app_tensorSections_apply M χ W a t
  rw [← germ_res_mem_maximalIdeal_smul_iff (M ⊗ N') (le_top : W ≤ ⊤) hy, e1]
  exact hf.germ_tensorSections_mem_maximalIdeal_smul_iff_left N' hy (χ.app W t)

end AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
  {L : LineBundle ρ.source.toVariety} {κ : ℕ}

/-- The closed immersion `𝒵 ↪ Tot(A^{⊕(N+1)})` of the twisted affine cone (the `coneι` of `coneCoordinate`). -/
noncomputable def BasedJet.coneι (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f] :
    (MMSetup.cone f).left ⟶
      (AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).left :=
  (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
    (homogeneousEquationSection (seedLineBundle X.embedding f) X.embDim (D.E.F j) (D.E.homogeneous j))).subschemeι

theorem BasedJet.coneι_comp_hom (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f] :
    BasedJet.coneι f ≫ (AlgebraicGeometry.Scheme.totalSpace
      (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom =
      (MMSetup.cone f).hom := rfl

/-- `J ≫ coneι` as a `C`-morphism `(p ≫ ρ) ⟶ Tot(A^{⊕(N+1)})` (the `toTot` of `coneCoordinate`). -/
noncomputable def BasedJet.toTot (J : BasedJet f ρ L κ) :
    CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom) ⟶
      AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1)) :=
  CategoryTheory.Over.homMk (J.hom ≫ BasedJet.coneι f) (by
    change (J.hom ≫ BasedJet.coneι f) ≫ (AlgebraicGeometry.Scheme.totalSpace
      (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom =
      jetNeighborhood.proj L κ ≫ ρ.hom
    rw [Category.assoc, BasedJet.coneι_comp_hom]
    exact J.over)

/-- `coneCoordinate` unfolded: `p^*ρ^*θ'` of `(pullbackComp p ρ)⁻¹` of the `ℓ`-th coordinate of
`totalSpaceHomEquiv (J ≫ coneι)`. -/
theorem BasedJet.coneCoordinate_eq (J : BasedJet f ρ L κ) (ℓ : Fin (X.embDim + 1)) :
    J.coneCoordinate ℓ =
      ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).map
          ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).map
            ((AlgebraicGeometry.Scheme.Modules.pullback f).map
              (CategoryTheory.eqToHom (X.OX_toModules 1).symm)))).app ⊤
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp (jetNeighborhood.proj L κ) ρ.hom).inv.app
            (seedLineBundle X.embedding f)).app ⊤
          (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ ≫ ρ.hom)).map
              (CategoryTheory.Limits.biproduct.π (fun _ : Fin (X.embDim + 1) => seedLineBundle X.embedding f) ℓ :
                AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1) ⟶
                  seedLineBundle X.embedding f)).app ⊤
            (AlgebraicGeometry.Scheme.totalSpaceHomEquiv
              (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))
              (CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom)) J.toTot))) := rfl

/-- **The cone coordinate in a frame** (proof of Lemma 3.1 of the paper): for a frame `a` of `A = f^*O(1)` on `U ⊆ C`,
on `p⁻¹ρ⁻¹U` the cone coordinate `P_ℓ = coneCoordinate J ℓ` is `c • η_p(η_ρ(θ' a))` with
`c = (J ≫ coneι)^♯(x_ℓ^{a^∨}) ∈ Γ(C̃_(κ)(L), p⁻¹ρ⁻¹U)`. -/
theorem BasedJet.coneCoordinate_res_eq_smul (J : BasedJet f ρ L κ) (ℓ : Fin (X.embDim + 1)) (U : C.toScheme.Opens)
    {a : Γ(seedLineBundle X.embedding f, U)}
    (hf : AlgebraicGeometry.Scheme.Modules.IsFrame (seedLineBundle X.embedding f) U a) :
    ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules).res
        (le_top : jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U) ≤ ⊤) (J.coneCoordinate ℓ) =
      (J.hom ≫ BasedJet.coneι f).appLE
          ((AlgebraicGeometry.Scheme.totalSpace
            (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U)
          (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U))
          (AlgebraicGeometry.Scheme.totalSpace.preimage_le_of_over
            (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))
            (CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom)) J.toTot U)
          (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction (seedLineBundle X.embedding f) (X.embDim + 1) ℓ U
            hf.dualSec) •
        (show Γ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
            (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
              (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules,
            jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) from
          ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (jetNeighborhood.proj L κ)).unit.app
            ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj
              ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (X.OX 1).toModules))).app (ρ.hom ⁻¹ᵁ U)
            (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).unit.app
              ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (X.OX 1).toModules)).app U
              (((AlgebraicGeometry.Scheme.Modules.pullback f).map
                (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).app U a))) := by
  have s1 := AlgebraicGeometry.Scheme.totalSpace.totalSpaceHomEquiv_coordinate_res_eq_smul
    (seedLineBundle X.embedding f) (X.embDim + 1) (CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom))
    J.toTot ℓ U hf
  rw [BasedJet.coneCoordinate_eq]
  exact AlgebraicGeometry.Scheme.Modules.res_pullback_map_pullbackComp_inv_of_res_eq_smul
    (jetNeighborhood.proj L κ) ρ.hom
    ((AlgebraicGeometry.Scheme.Modules.pullback f).map (CategoryTheory.eqToHom (X.OX_toModules 1).symm)) U a _ _ s1

omit D in
/-- `a_M := η_ρ(θ' a)` is a frame of `M = ρ^*f^*O(1)` on `ρ⁻¹U` when `a` is a frame of `A` on `U`. -/
theorem BasedJet.isFrame_unit_unit_map (U : C.toScheme.Opens) {a : Γ(seedLineBundle X.embedding f, U)}
    (hf : AlgebraicGeometry.Scheme.Modules.IsFrame (seedLineBundle X.embedding f) U a) :
    AlgebraicGeometry.Scheme.Modules.IsFrame
      (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
        (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules (ρ.hom ⁻¹ᵁ U)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).unit.app
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (X.OX 1).toModules)).app U
        (((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).app U a)) :=
  MiyaokaMori.DualPullback.isFrame_unitSec_pullback ρ.hom _
    (hf.map_iso ((AlgebraicGeometry.Scheme.Modules.pullback f).mapIso (CategoryTheory.eqToIso (X.OX_toModules 1).symm)))

/-- **Step (4) of `exists_pieceSection_generatesAt`**: on `W = ρ⁻¹U`,
`pullbackSectionToPushforward p M (coneCoordinate J ℓ) = a_M ⊗ (J ≫ coneι)^♯(x_ℓ^{a^∨})`. -/
theorem BasedJet.pullbackSectionToPushforward_coneCoordinate_res (J : BasedJet f ρ L κ) (ℓ : Fin (X.embDim + 1))
    (U : C.toScheme.Opens) {a : Γ(seedLineBundle X.embedding f, U)}
    (hf : AlgebraicGeometry.Scheme.Modules.IsFrame (seedLineBundle X.embedding f) U a) :
    ((LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
        (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules ⊗
      (AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
        (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).res (le_top : ρ.hom ⁻¹ᵁ U ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ)
          (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
            (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules (J.coneCoordinate ℓ)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
        ((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
          (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)) (ρ.hom ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ρ.hom).unit.app
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (X.OX 1).toModules)).app U
          (((AlgebraicGeometry.Scheme.Modules.pullback f).map
            (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).app U a))
        (show Γ((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
            (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf), ρ.hom ⁻¹ᵁ U) from
          (J.hom ≫ BasedJet.coneι f).appLE
            ((AlgebraicGeometry.Scheme.totalSpace
              (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U)
            (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U))
            (AlgebraicGeometry.Scheme.totalSpace.preimage_le_of_over
              (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))
              (CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom)) J.toTot U)
            (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction (seedLineBundle X.embedding f) (X.embDim + 1) ℓ U
              hf.dualSec)) :=
  AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_res_eq_tensorSections (jetNeighborhood.proj L κ)
    (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules (J.coneCoordinate ℓ)
    (ρ.hom ⁻¹ᵁ U) _ _ (J.coneCoordinate_res_eq_smul ℓ U hf)

/-- `J.coefficient ℓ m` unfolded for `m ≤ κ`: `((M ◁ χ_m) ≫ Φ')(pullbackSectionToPushforward p M (coneCoordinate J ℓ))`. -/
theorem BasedJet.coefficient_eq (J : BasedJet f ρ L κ) (ℓ : Fin (X.embDim + 1)) (m : ℕ) (hm : m ≤ κ) :
    J.coefficient ℓ m =
      (CategoryTheory.MonoidalCategoryStruct.whiskerLeft
          (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
            (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
          ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
            CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
              ⟨m, Nat.lt_succ_of_le hm⟩ ≫
            (truncatedJetAlgebra.pieceIso L m).hom ≫
            (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).hom) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
            (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
          (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m)).inv ≫
        (L.coefficientModuleIso
          (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
            (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) m).hom).app ⊤
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ)
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules (J.coneCoordinate ℓ)) := by
  unfold BasedJet.coefficient xiCoefficientThickening
  rw [dif_pos hm]
  rfl

/-- **Existence of a piece section generating at a point, unfolded form.** If `J.coefficient ℓ m` (`m ≤ κ`) does not vanish
at `y`, there are an affine open `U ∋ ρ(y)` and a function `b ∈ Γ(𝒵, π⁻¹U)` (the `ℓ`-th coordinate function of a
frame of `A` on `U`, restricted to the cone) such that the `m`-th `ξ`-coefficient of `J^♯ b`
(`structureIso⁻¹ ≫ π_m ≫ pieceIso`, i.e. `J.pieceSection U m _ b`) has germ at `y` outside `𝔪_y • ⊤`.
See the module docstring for the proof. -/
theorem BasedJet.exists_pieceSection_germ_notMem_of_not_isZeroAt (J : BasedJet f ρ L κ) (y : ρ.source.toScheme)
    (ℓ : Fin (X.embDim + 1)) (m : ℕ) (hm : m ≤ κ) (h : ¬ IsZeroAt (J.coefficient ℓ m) y) :
    ∃ (U : C.toScheme.AffineZariskiSite) (hy : y ∈ ρ.hom ⁻¹ᵁ U.1)
      (b : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1)),
      (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ
          (ρ.hom ⁻¹ᵁ U.1) y hy
          ((((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
              CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
                ⟨m, Nat.lt_succ_of_le hm⟩ ≫
              (truncatedJetAlgebra.pieceIso L m).hom).val.app (Opposite.op (ρ.hom ⁻¹ᵁ U.1))).hom
            (show (((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
                (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf)).val.obj
                  (Opposite.op (ρ.hom ⁻¹ᵁ U.1)) : Type u) from
              (J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ U.1) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U.1)) (by
                rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage,
                  J.over])).hom b)) ∉
        (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
          (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
            ((AlgebraicGeometry.Scheme.Modules.monoidalPow
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.stalk y)) := by
  obtain ⟨U, hUaff, -, hyU, a, hf⟩ := AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le
    (seedLineBundle X.embedding f) (show ρ.hom.base y ∈ (⊤ : C.toScheme.Opens) from trivial)
  have hleb : (MMSetup.cone f).hom ⁻¹ᵁ U ≤ BasedJet.coneι f ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U) :=
    le_of_eq rfl
  refine ⟨⟨U, hUaff⟩, hyU, AlgebraicGeometry.Scheme.totalSpace.coordinateFunctionOn (seedLineBundle X.embedding f)
    (X.embDim + 1) ℓ U hf.dualSec (BasedJet.coneι f) ((MMSetup.cone f).hom ⁻¹ᵁ U) hleb, ?_⟩
  intro hmem
  apply h
  rw [J.coefficient_eq ℓ m hm]
  refine isZeroAt_hom_app
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
        (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m)).inv ≫
      (L.coefficientModuleIso
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) m).hom)
    ((CategoryTheory.MonoidalCategoryStruct.whiskerLeft
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
        ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
          CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨m, Nat.lt_succ_of_le hm⟩ ≫
          (truncatedJetAlgebra.pieceIso L m).hom ≫
          (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).hom)).app ⊤
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward (jetNeighborhood.proj L κ)
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules (J.coneCoordinate ℓ)))
    y ?_
  refine (AlgebraicGeometry.Scheme.Modules.germ_whiskerLeft_app_mem_maximalIdeal_smul_iff_of_res_eq_tensorSections
    ((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨m, Nat.lt_succ_of_le hm⟩ ≫
      (truncatedJetAlgebra.pieceIso L m).hom ≫
      (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).hom)
    _ hyU (BasedJet.isFrame_unit_unit_map U hf) _ (J.pullbackSectionToPushforward_coneCoordinate_res ℓ U hf)).mpr ?_
  refine (AlgebraicGeometry.Scheme.Modules.germ_hom_app_mem_maximalIdeal_smul_iff_of_iso
    (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m) (ρ.hom ⁻¹ᵁ U) hyU
    (((AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)).inv ≫
      CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨m, Nat.lt_succ_of_le hm⟩ ≫
      (truncatedJetAlgebra.pieceIso L m).hom).app (ρ.hom ⁻¹ᵁ U)
      (show Γ((AlgebraicGeometry.Scheme.Modules.pushforward (jetNeighborhood.proj L κ)).obj
          (SheafOfModules.unit (jetNeighborhood L κ).left.ringCatSheaf), ρ.hom ⁻¹ᵁ U) from
        (J.hom ≫ BasedJet.coneι f).appLE
          ((AlgebraicGeometry.Scheme.totalSpace
            (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U)
          (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U))
          (AlgebraicGeometry.Scheme.totalSpace.preimage_le_of_over
            (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))
            (CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom)) J.toTot U)
          (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction (seedLineBundle X.embedding f) (X.embDim + 1) ℓ U
            hf.dualSec)))).mpr ?_
  have hc : (J.hom.appLE ((MMSetup.cone f).hom ⁻¹ᵁ U) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) (by
        rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage,
          J.over])).hom
      (AlgebraicGeometry.Scheme.totalSpace.coordinateFunctionOn (seedLineBundle X.embedding f)
        (X.embDim + 1) ℓ U hf.dualSec (BasedJet.coneι f) ((MMSetup.cone f).hom ⁻¹ᵁ U) hleb) =
      (J.hom ≫ BasedJet.coneι f).appLE
        ((AlgebraicGeometry.Scheme.totalSpace
          (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U)
        (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U))
        (AlgebraicGeometry.Scheme.totalSpace.preimage_le_of_over
          (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))
          (CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom)) J.toTot U)
        (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction (seedLineBundle X.embedding f) (X.embDim + 1) ℓ U
          hf.dualSec) :=
    ConcreteCategory.congr_hom (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE J.hom (BasedJet.coneι f)
      ((AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U)
      ((MMSetup.cone f).hom ⁻¹ᵁ U) (jetNeighborhood.proj L κ ⁻¹ᵁ (ρ.hom ⁻¹ᵁ U)) hleb
      (by rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, ← AlgebraicGeometry.Scheme.Hom.comp_preimage, J.over]))
      (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction (seedLineBundle X.embedding f) (X.embDim + 1) ℓ U
        hf.dualSec)
  rw [hc] at hmem
  exact hmem

end
