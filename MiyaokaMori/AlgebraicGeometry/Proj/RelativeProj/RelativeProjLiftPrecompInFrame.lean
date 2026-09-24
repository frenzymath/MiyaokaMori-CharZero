import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftPrecomp
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensorPow

/-! # The adjoint transpose of `precompΨ` on sections, read in a frame

`precompΨ g Ψ m = C⁻¹ ≫ g^*Ψ_m ≫ pullbackMonoidalPow` (`RelativeProjLiftPrecomp.lean`) is the `Ψ` of
`BasedJet.genericLiftData` (with `g = η : Spec κ(η_{C̃}) → C̃`). If the adjoint transpose `Ψ̃_m(x)` of
`Ψ_m` at `x ∈ Γ(W, S_m)` restricts on `U ⊆ f⁻¹W` to `r • t^{⊗m}`, then the adjoint transpose of
`precompΨ g Ψ m` at `x` restricts on `g⁻¹U` to `g^♯(r) • (η_g t)^{⊗m}` (`sectionPow`, `unitSec`).
Proof: `Adjunction.homEquiv_unit`, `pullbackComp_inv_app_unit`, naturality of the unit, `unit_app_map`,
`Hom.app_smul`, `pullbackMonoidalPow_app_unitSec_sectionPow`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry.Scheme.Modules

variable {X T T' : AlgebraicGeometry.Scheme.{u}}

/-- `g^*ψ` on unit sections (naturality of the unit); private copy of
`Modules.pullback_map_app_unitSec` (`…_GenericCoordsOfFrame_LiftPiece`). -/
private theorem pullback_map_app_unitSec_pc (g : T' ⟶ T) {A B : T.Modules} (ψ : A ⟶ B) (U : T.Opens)
    (a : Γ(A, U)) :
    Modules.Hom.app ((Modules.pullback g).map ψ) (g ⁻¹ᵁ U) (MiyaokaMori.DualPullback.unitSec g A a) =
      MiyaokaMori.DualPullback.unitSec g B (Modules.Hom.app ψ U a) := by
  have h := (Modules.pullbackPushforwardAdjunction g).unit.naturality ψ
  exact (congrArg (fun χ : A ⟶ (Modules.pushforward g).obj ((Modules.pullback g).obj B) =>
    Modules.Hom.app χ U a) h).symm

/-- The adjoint transpose on sections: `Ψ̃(x) = Ψ(η x)`; private copy of
`Modules.homEquiv_app_eq_app_unitSec` (`…_GenericCoordsOfFrame_LiftPiece`). -/
private theorem homEquiv_app_eq_app_unitSec_pc (f : T ⟶ X) {A : X.Modules} {B : T.Modules}
    (Ψ : (Modules.pullback f).obj A ⟶ B) (W : X.Opens) (x : Γ(A, W)) :
    (Modules.Hom.app ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _ Ψ) W x : Γ(B, f ⁻¹ᵁ W)) =
      Modules.Hom.app Ψ (f ⁻¹ᵁ W) (MiyaokaMori.DualPullback.unitSec f A x) :=
  congrArg (fun χ : A ⟶ (Modules.pushforward f).obj B => Modules.Hom.app χ W x)
    (Adjunction.homEquiv_unit (Modules.pullbackPushforwardAdjunction f) A B Ψ)

/-- **`precompΨ` in a frame.** -/
theorem res_homEquiv_precompΨ_app_eq_smul_sectionPow
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (Ψ : ∀ m : ℕ, (Modules.pullback f).obj (S.part m) ⟶ Modules.monoidalPow M m) (g : T' ⟶ T)
    (m : ℕ) (W : X.Opens) (x : S.sectionsPiece W m) (U : T.Opens) (hU : U ≤ f ⁻¹ᵁ W)
    (t : Γ(M, U)) (r : Γ(T, U))
    (hx : (Modules.monoidalPow M m).res hU
        (Modules.Hom.app ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (Ψ m)) W x :
          Γ(Modules.monoidalPow M m, f ⁻¹ᵁ W)) =
      r • Modules.sectionPow M U t m)
    (hgU : g ⁻¹ᵁ U ≤ (g ≫ f) ⁻¹ᵁ W) :
    (Modules.monoidalPow ((Modules.pullback g).obj M) m).res hgU
        (Modules.Hom.app ((Modules.pullbackPushforwardAdjunction (g ≫ f)).homEquiv _ _
            (precompΨ g Ψ m)) W x :
          Γ(Modules.monoidalPow ((Modules.pullback g).obj M) m, (g ≫ f) ⁻¹ᵁ W)) =
      g.app U r • Modules.sectionPow ((Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (MiyaokaMori.DualPullback.unitSec g M t) m := by
  set Ψx : Γ(Modules.monoidalPow M m, f ⁻¹ᵁ W) :=
    Modules.Hom.app ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (Ψ m)) W x with hΨx
  have h0 : (Modules.Hom.app ((Modules.pullbackPushforwardAdjunction (g ≫ f)).homEquiv _ _
        (precompΨ g Ψ m)) W x :
        Γ(Modules.monoidalPow ((Modules.pullback g).obj M) m, (g ≫ f) ⁻¹ᵁ W)) =
      Modules.Hom.app (Modules.pullbackMonoidalPow g M m) ((g ≫ f) ⁻¹ᵁ W)
        (MiyaokaMori.DualPullback.unitSec g (Modules.monoidalPow M m) Ψx) := by
    refine (homEquiv_app_eq_app_unitSec_pc (g ≫ f) (precompΨ g Ψ m) W x).trans ?_
    show Modules.Hom.app (Modules.pullbackMonoidalPow g M m) ((g ≫ f) ⁻¹ᵁ W)
      (Modules.Hom.app ((Modules.pullback g).map (Ψ m)) ((g ≫ f) ⁻¹ᵁ W)
        (Modules.Hom.app ((Modules.pullbackComp g f).inv.app (S.part m)) ((g ≫ f) ⁻¹ᵁ W)
          (MiyaokaMori.DualPullback.unitSec (g ≫ f) (S.part m) x))) = _
    refine congrArg (fun z => Modules.Hom.app (Modules.pullbackMonoidalPow g M m) ((g ≫ f) ⁻¹ᵁ W) z) ?_
    refine (congrArg (fun z => Modules.Hom.app ((Modules.pullback g).map (Ψ m)) ((g ≫ f) ⁻¹ᵁ W) z)
      (Modules.pullbackComp_inv_app_unit g f (S.part m) W x)).trans ?_
    exact (pullback_map_app_unitSec_pc g (Ψ m) (f ⁻¹ᵁ W)
      (MiyaokaMori.DualPullback.unitSec f (S.part m) x)).trans
      (congrArg (MiyaokaMori.DualPullback.unitSec g (Modules.monoidalPow M m))
        (homEquiv_app_eq_app_unitSec_pc f (Ψ m) W x).symm)
  rw [h0, ← Modules.Hom.app_res]
  have e2 : ((Modules.pullback g).obj (Modules.monoidalPow M m)).res hgU
      (MiyaokaMori.DualPullback.unitSec g (Modules.monoidalPow M m) Ψx) =
      MiyaokaMori.DualPullback.unitSec g (Modules.monoidalPow M m) ((Modules.monoidalPow M m).res hU Ψx) :=
    (Modules.unit_app_map g (Modules.monoidalPow M m) hU Ψx).symm
  rw [e2, hx, MiyaokaMori.DualPullback.unitSec_smul, Modules.Hom.app_smul,
    Modules.pullbackMonoidalPow_app_unitSec_sectionPow]

end AlgebraicGeometry.Scheme.relativeProj

end
