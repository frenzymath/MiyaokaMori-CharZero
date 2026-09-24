import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftData
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensorPow

/-! # The local ring map of a `relativeProj.lift`, read in a frame

General form of the computation behind `BasedJet.exists_genericTrivialization_of_frame`, at the variable
level of `relativeProj.liftLocalPieceAux D ι e' W hW m x` (`RelativeProjLiftData.lean`): if the adjoint
transpose `Ψ̃_m(x) ∈ Γ(f⁻¹W, M^{⊗m})` of `D.Ψ m` at `x` restricts on `W_T ⊆ f⁻¹W` to `r • t^{⊗m}`
(`sectionPow`), `ι` lands in `W_T`, and the trivialization `e'` sends `η(t)|_⊤` to `1`, then the value
of the local ring map at `x` is `ι^♯(r) = ι.appLE W_T ⊤ r`.

Proof: `liftLocalHomAux = C⁻¹ ≫ ι^*Ψ_m ≫ P ≫ E ≫ K`. On the unit section `η_{ι≫f}(x)`: `C⁻¹` gives
`η_ι(η_f x)` (`pullbackComp_inv_app_unit`), `ι^*Ψ_m` gives `η_ι(Ψ̃_m x)` (unit naturality +
`Adjunction.homEquiv_unit`); restricting to `ι⁻¹W_T` and using the hypothesis, this is
`ι^♯r • η_ι(t^{⊗m})` (`unit_app_map`, `Hom.app_smul`); `P` turns `η_ι(t^{⊗m})` into `η_ι(t)^{⊗m}`
(`pullbackMonoidalPow_app_unitSec_sectionPow`), restriction to `⊤` commutes with everything
(`Hom.app_res`, `sectionPow_res`), `E` gives `e'(η_ι t|_⊤)^{⊗m} = 1^{⊗m}` and `K` gives `1`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {Y T : AlgebraicGeometry.Scheme.{u}}

/-- `g^*ψ` on unit sections: `g^*ψ (η a) = η (ψ a)` (naturality of the unit). -/
theorem pullback_map_app_unitSec (g : Y ⟶ T) {A B : T.Modules} (ψ : A ⟶ B) (U : T.Opens) (a : Γ(A, U)) :
    ((pullback g).map ψ).app (g ⁻¹ᵁ U) (MiyaokaMori.DualPullback.unitSec g A a) =
      MiyaokaMori.DualPullback.unitSec g B (ψ.app U a) := by
  have h := (pullbackPushforwardAdjunction g).unit.naturality ψ
  exact (congrArg (fun χ : A ⟶ (pushforward g).obj ((pullback g).obj B) => χ.app U a) h).symm

/-- The adjoint transpose on sections: `Ψ̃(x) = Ψ(η x)`. -/
theorem homEquiv_app_eq_app_unitSec (f : T ⟶ Y) {A : Y.Modules} {B : T.Modules}
    (Ψ : (pullback f).obj A ⟶ B) (W : Y.Opens) (x : Γ(A, W)) :
    (Hom.app ((pullbackPushforwardAdjunction f).homEquiv _ _ Ψ) W x : Γ(B, f ⁻¹ᵁ W)) =
      Hom.app Ψ (f ⁻¹ᵁ W) (MiyaokaMori.DualPullback.unitSec f A x) :=
  congrArg (fun χ : A ⟶ (pushforward f).obj B => χ.app W x)
    (Adjunction.homEquiv_unit (pullbackPushforwardAdjunction f) A B Ψ)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry.Scheme.Modules

variable {X T Y : AlgebraicGeometry.Scheme.{u}}

/-- **The local ring map of the lift in a frame.** -/
theorem liftLocalPieceAux_eq_appLE_of_res_eq_smul_sectionPow
    {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
    (D : LiftData S f M) (ι : Y ⟶ T)
    (e' : (pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (m : ℕ) (x : S.sectionsPiece W m)
    (W_T : T.Opens) (hWT : W_T ≤ f ⁻¹ᵁ W) (hι : (⊤ : Y.Opens) ≤ ι ⁻¹ᵁ W_T)
    (t : Γ(M, W_T)) (r : Γ(T, W_T))
    (hx : (monoidalPow M m).res hWT
        (Modules.Hom.app ((pullbackPushforwardAdjunction f).homEquiv _ _ (D.Ψ m)) W x :
          Γ(monoidalPow M m, f ⁻¹ᵁ W)) =
      r • sectionPow M W_T t m)
    (he : Modules.Hom.app e'.hom ⊤ (((pullback ι).obj M).res hι (MiyaokaMori.DualPullback.unitSec ι M t)) =
      (1 : Γ(Y, ⊤))) :
    liftLocalPieceAux D ι e' W hW m x = ι.appLE W_T ⊤ hι r := by
  -- notation
  set u₀ : Γ((pullback (ι ≫ f)).obj (S.part m), (ι ≫ f) ⁻¹ᵁ W) :=
    MiyaokaMori.DualPullback.unitSec (ι ≫ f) (S.part m) x with hu₀
  set Ψx : Γ(monoidalPow M m, f ⁻¹ᵁ W) :=
    Modules.Hom.app ((pullbackPushforwardAdjunction f).homEquiv _ _ (D.Ψ m)) W x with hΨx
  have h2 : ι ⁻¹ᵁ W_T ≤ (ι ≫ f) ⁻¹ᵁ W := fun y hy => hWT hy
  set Φ₁ : (pullback (ι ≫ f)).obj (S.part m) ⟶ monoidalPow ((pullback ι).obj M) m :=
    (pullbackComp ι f).inv.app (S.part m) ≫ (pullback ι).map (D.Ψ m) ≫ pullbackMonoidalPow ι M m
    with hΦ₁
  set Φ₂ : monoidalPow ((pullback ι).obj M) m ⟶ SheafOfModules.unit Y.ringCatSheaf :=
    monoidalPowMap e'.hom m ≫ unitPowCollapse Y m with hΦ₂
  have hΦ : liftLocalHomAux D ι e' m = Φ₁ ≫ Φ₂ := by
    rw [hΦ₁, hΦ₂]; simp only [liftLocalHomAux, Category.assoc]
  -- the value, unfolded, with the restriction split as ⊤ ≤ ι⁻¹W_T ≤ (ι≫f)⁻¹W
  have hdef : liftLocalPieceAux D ι e' W hW m x =
      Modules.Hom.app Φ₂ ⊤ (Modules.Hom.app Φ₁ ⊤
        (((pullback (ι ≫ f)).obj (S.part m)).res hι (((pullback (ι ≫ f)).obj (S.part m)).res h2 u₀))) := by
    show Modules.Hom.app (liftLocalHomAux D ι e' m) ⊤ (((pullback (ι ≫ f)).obj (S.part m)).res hW u₀) = _
    rw [hΦ, res_res]
    rfl
  rw [hdef]
  -- Φ₁ on u₀ restricted to ι⁻¹W_T
  have hΦ₁u : Modules.Hom.app Φ₁ (ι ⁻¹ᵁ W_T) (((pullback (ι ≫ f)).obj (S.part m)).res h2 u₀) =
      (ι.app W_T r) • sectionPow ((pullback ι).obj M) (ι ⁻¹ᵁ W_T)
        (MiyaokaMori.DualPullback.unitSec ι M t) m := by
    calc Modules.Hom.app Φ₁ (ι ⁻¹ᵁ W_T) (((pullback (ι ≫ f)).obj (S.part m)).res h2 u₀)
        = Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T)
            (Modules.Hom.app ((pullback ι).map (D.Ψ m)) (ι ⁻¹ᵁ W_T)
              (Modules.Hom.app ((pullbackComp ι f).inv.app (S.part m)) (ι ⁻¹ᵁ W_T)
                (((pullback (ι ≫ f)).obj (S.part m)).res h2 u₀))) := rfl
      _ = Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T)
            (Modules.Hom.app ((pullback ι).map (D.Ψ m)) (ι ⁻¹ᵁ W_T)
              (((pullback ι).obj ((pullback f).obj (S.part m))).res h2
                (Modules.Hom.app ((pullbackComp ι f).inv.app (S.part m)) ((ι ≫ f) ⁻¹ᵁ W) u₀))) := by
          exact congrArg (fun z => Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T)
            (Modules.Hom.app ((pullback ι).map (D.Ψ m)) (ι ⁻¹ᵁ W_T) z))
            (Hom.app_res ((pullbackComp ι f).inv.app (S.part m)) h2 u₀)
      _ = Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T)
            (((pullback ι).obj (monoidalPow M m)).res h2
              (Modules.Hom.app ((pullback ι).map (D.Ψ m)) ((ι ≫ f) ⁻¹ᵁ W)
                (Modules.Hom.app ((pullbackComp ι f).inv.app (S.part m)) ((ι ≫ f) ⁻¹ᵁ W) u₀))) := by
          exact congrArg (fun z => Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T) z)
            (Hom.app_res ((pullback ι).map (D.Ψ m)) h2 _)
      _ = Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T)
            (((pullback ι).obj (monoidalPow M m)).res h2
              (MiyaokaMori.DualPullback.unitSec ι (monoidalPow M m) Ψx)) := by
          refine congrArg (fun z => Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T)
            (((pullback ι).obj (monoidalPow M m)).res h2 z)) ?_
          refine (congrArg (fun z => Modules.Hom.app ((pullback ι).map (D.Ψ m)) ((ι ≫ f) ⁻¹ᵁ W) z)
            (pullbackComp_inv_app_unit ι f (S.part m) W x)).trans ?_
          exact (pullback_map_app_unitSec ι (D.Ψ m) (f ⁻¹ᵁ W)
            (MiyaokaMori.DualPullback.unitSec f (S.part m) x)).trans
            (congrArg (MiyaokaMori.DualPullback.unitSec ι (monoidalPow M m))
              (homEquiv_app_eq_app_unitSec f (D.Ψ m) W x).symm)
      _ = Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T)
            (MiyaokaMori.DualPullback.unitSec ι (monoidalPow M m) ((monoidalPow M m).res hWT Ψx)) := by
          exact congrArg (fun z => Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T) z)
            (unit_app_map ι (monoidalPow M m) hWT Ψx).symm
      _ = Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T)
            (MiyaokaMori.DualPullback.unitSec ι (monoidalPow M m) (r • sectionPow M W_T t m)) := by
          rw [hx]
      _ = Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T)
            (ι.app W_T r • MiyaokaMori.DualPullback.unitSec ι (monoidalPow M m) (sectionPow M W_T t m)) := by
          rw [MiyaokaMori.DualPullback.unitSec_smul]
      _ = ι.app W_T r • Modules.Hom.app (pullbackMonoidalPow ι M m) (ι ⁻¹ᵁ W_T)
            (MiyaokaMori.DualPullback.unitSec ι (monoidalPow M m) (sectionPow M W_T t m)) :=
          Hom.app_smul _ _ _
      _ = ι.app W_T r • sectionPow ((pullback ι).obj M) (ι ⁻¹ᵁ W_T)
            (MiyaokaMori.DualPullback.unitSec ι M t) m := by
          rw [pullbackMonoidalPow_app_unitSec_sectionPow]
  -- Φ₂ on `c • v^{⊗m}` with `e'(v) = 1` is `c`
  have hΦ₂u : ∀ (c : Γ(Y, ⊤)) (v : Γ((pullback ι).obj M, ⊤)), Modules.Hom.app e'.hom ⊤ v = (1 : Γ(Y, ⊤)) →
      Modules.Hom.app Φ₂ ⊤ (c • sectionPow ((pullback ι).obj M) ⊤ v m) = c := by
    intro c v hv
    show Modules.Hom.app (unitPowCollapse Y m) ⊤
      (Modules.Hom.app (monoidalPowMap e'.hom m) ⊤ (c • sectionPow ((pullback ι).obj M) ⊤ v m)) = c
    rw [Hom.app_smul, monoidalPowMap_app_sectionPow, hv, Hom.app_smul]
    exact (congrArg (fun z : Γ(Y, ⊤) => c • z) (unitPowCollapse_app_sectionPow_one (X := Y) ⊤ m)).trans
      (mul_one c)
  rw [Hom.app_res, hΦ₁u, res_smul]
  refine (congrArg (fun z => Modules.Hom.app Φ₂ ⊤ (Y.presheaf.map (homOfLE hι).op (ι.app W_T r) • z))
    (sectionPow_res ((pullback ι).obj M) hι (MiyaokaMori.DualPullback.unitSec ι M t) m)).trans ?_
  exact hΦ₂u _ _ he

end AlgebraicGeometry.Scheme.relativeProj

end
