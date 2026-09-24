import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftData
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftDataOfEpi
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseDegreeOne
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.EpiOfTransposeFrames
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.FrameLocusCoordinate

/-! # Degree one of the local ring map of `X → P(E)`

For the lift data `D := liftDataOfEpi f E M ψ hψ` of an epimorphism `ψ : f^*E ↠ M` (Stacks 01O9), the local ring map
`Φ = liftLocalRingHomAux D ι et V : A(V) = ⊕_m Γ(V, Sym^m E) → Γ(Y, O)` of a piece `(ι : Y ⟶ X, et : ι^*M ≅ O_Y)`
sends the degree-one generator `π₁(e) = (symGen E).app V e` (`e ∈ E(V)`) to the **coordinate of the section
`φ(e) = ψ^♭(e) ∈ Γ(M, f⁻¹V)`** through the trivialization `et` (`coordOn`, `…_FrameCoord.lean`).

* Sheaf level (`pullback_map_symGen_comp_liftLocalHomAux_one`): `(ι ≫ f)^*(symGen E) ≫ Φ₁ = C⁻¹ ≫ ι^*ψ ≫ et.hom`
  — the same script as `projBundle.pullback_map_symGen_comp_localRingHomSheafHom_one`
  (`TotLineAffineOverBaseDegreeOne.lean`), with `Ψ₁ = symGradedPullbackDesc f ψ 1` and
  `pullback_map_symGen_comp_symGradedPullbackDesc_one` (degree 1 of `Sym ψ` is `ψ`), then the oplax left unitality of
  `ι^*`.
* Section level (`liftLocalPieceAux_one_symGen_app`): unwind `liftLocalPieceAux` (`liftLocalPieceAux_apply`): the unit
  `η_{ι≫f}` is natural in the module (`Adjunction.unit_naturality`), `C⁻¹` turns `η_{ι≫f}` into `η_ι ∘ η_f`
  (`pullbackComp_inv_app_unit`), `ι^*ψ` commutes with `η_ι` (`unit_naturality_app`), and `ψ(η_f e) = φ(e)`
  (`app_unit_app_eq_homEquiv_app`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj

open AlgebraicGeometry.Scheme.Modules

variable {X S Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (M : X.Modules) [M.IsLineBundle]
  (E : S.Modules) [E.IsQuasicoherent] (ψ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj E ⟶ M)
  (hψ : CategoryTheory.Epi ψ) (ι : Y ⟶ X)
  (et : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)

/-- `(f ≫ g).app U x = g.app U (f.app U x)` (`Hom.comp_app`). -/
private theorem comp_app_apply_d1 {A B D : Y.Modules} (φ : A ⟶ B) (χ : B ⟶ D) (U : Y.Opens) (x : Γ(A, U)) :
    (φ ≫ χ).app U x = χ.app U (φ.app U x) := by
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]

/-- **Degree one of the local sheaf map is `ψ` read through the trivialization**:
`(ι ≫ f)^*(symGen E) ≫ Φ₁ = (pullbackComp ι f).inv.app E ≫ ι^*ψ ≫ et.hom`. -/
theorem pullback_map_symGen_comp_liftLocalHomAux_one :
    (AlgebraicGeometry.Scheme.Modules.pullback (ι ≫ f)).map (symGen E) ≫
        AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux
          (AlgebraicGeometry.Scheme.relativeProj.liftDataOfEpi f E M ψ hψ) ι et 1 =
      (AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app E ≫
        (AlgebraicGeometry.Scheme.Modules.pullback ι).map ψ ≫ et.hom := by
  have hq : E.IsQuasicoherent := inferInstance
  unfold AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux
  have E1 := (AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.naturality_assoc (symGen E)
    ((AlgebraicGeometry.Scheme.Modules.pullback ι).map
        ((AlgebraicGeometry.Scheme.relativeProj.liftDataOfEpi f E M ψ hψ).Ψ 1) ≫
      pullbackMonoidalPow ι M 1 ≫ monoidalPowMap et.hom 1 ≫ unitPowCollapse _ 1)
  refine E1.trans ?_
  refine congrArg (fun k => _ ≫ k) ?_
  rw [Functor.comp_map, ← Category.assoc, ← Functor.map_comp,
    AlgebraicGeometry.Scheme.relativeProj.liftDataOfEpi_Ψ,
    pullback_map_symGen_comp_symGradedPullbackDesc_one f E hq ψ]
  erw [Functor.map_comp]
  rw [Category.assoc]
  refine congrArg (fun k => _ ≫ k) ?_
  show (AlgebraicGeometry.Scheme.Modules.pullback ι).map (λ_ M).inv ≫
      (pullbackTensorObjHom ι (𝟙_ X.Modules) M ≫
        (pullbackUnitIso ι).hom ▷ (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M) ≫
      (𝟙 (𝟙_ _) ⊗ₘ et.hom) ≫ ((𝟙 (𝟙_ _) ▷ 𝟙_ _) ≫ (λ_ (𝟙_ _)).hom) = et.hom
  rw [pullbackTensorObjHom_eq_δ, ← pullback_η]
  exact AlgebraicGeometry.Scheme.projBundle.DegreeOneAux.oplax_leftUnitor_tensorHom_collapse
    (AlgebraicGeometry.Scheme.Modules.pullback ι) (inst := pullbackOplaxMonoidal ι) et.hom rfl _
    (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Degree one of the local ring map on the generator `π₁(e)` is the coordinate of `φ(e)`**:
`liftLocalPieceAux D ι et V hV 1 ((symGen E).app V e) = coordOn ι M et (φ e) hV`, where
`φ e = ofPushforwardSection f M ((homEquiv ψ).app V e) ∈ Γ(M, f⁻¹V)` is the transpose of `ψ` on `e`. -/
theorem liftLocalPieceAux_one_symGen_app (V : S.Opens) (hV : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ V) (e : Γ(E, V)) :
    AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux
        (AlgebraicGeometry.Scheme.relativeProj.liftDataOfEpi f E M ψ hψ) ι et V hV 1 ((symGen E).app V e) =
      coordOn ι M et (ofPushforwardSection f M
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E M ψ).app V e)) hV := by
  rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_apply]
  -- the unit is natural in the module: `η(π₁ e) = (g^*π₁)(η e)`, `g := ι ≫ f`
  have h1 : ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (ι ≫ f)).unit.app
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra E).part 1)).app V ((symGen E).app V e) =
      ((AlgebraicGeometry.Scheme.Modules.pullback (ι ≫ f)).map (symGen E)).app ((ι ≫ f) ⁻¹ᵁ V)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (ι ≫ f)).unit.app E).app V e) :=
    (unit_naturality_app (ι ≫ f) (symGen E) V e).symm
  change ((AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux
      (AlgebraicGeometry.Scheme.relativeProj.liftDataOfEpi f E M ψ hψ) ι et 1).app ⊤
      (((AlgebraicGeometry.Scheme.Modules.pullback (ι ≫ f)).obj _).res hV
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (ι ≫ f)).unit.app
          ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra E).part 1)).app V ((symGen E).app V e)))) = _
  rw [h1, ← Hom.app_res, ← comp_app_apply_d1, pullback_map_symGen_comp_liftLocalHomAux_one f M E ψ hψ ι et,
    comp_app_apply_d1, comp_app_apply_d1, Hom.app_res, Hom.app_res]
  unfold coordOn
  refine congrArg (et.hom.app ⊤) (congrArg (((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M).res hV) ?_)
  have h2 : ((AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).inv.app E).app ((ι ≫ f) ⁻¹ᵁ V)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (ι ≫ f)).unit.app E).app V e) =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj E)).app (f ⁻¹ᵁ V)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app V e) :=
    pullbackComp_inv_app_unit ι f E V e
  have h3 : ((AlgebraicGeometry.Scheme.Modules.pullback ι).map ψ).app ((ι ≫ f) ⁻¹ᵁ V)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj E)).app (f ⁻¹ᵁ V)
          (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app V e)) =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app (f ⁻¹ᵁ V)
        (ψ.app (f ⁻¹ᵁ V)
          (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app V e)) :=
    unit_naturality_app ι ψ (f ⁻¹ᵁ V) _
  rw [h2]
  exact h3.trans (congrArg (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app
    (f ⁻¹ᵁ V)) (app_unit_app_eq_homEquiv_app f ψ V e))

end AlgebraicGeometry.Scheme.relativeProj

end
