import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftData
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.RestrictToLambdaBundleFamilyTransition_PullbackSections
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeUnit
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence

/-! # Section-level dictionary for the tail `pullbackMonoidalPow ≫ monoidalPowMap ≫ unitPowCollapse`

Helper module for `RelativeProjLiftEvaluationTwistFamilyTransport.lean`.

Notation: `ι : Y ⟶ T`, `M : T.Modules`, `e' : ι^*M ≅ O_Y`,
`powTail n := pullbackMonoidalPow ι M n ≫ monoidalPowMap e'.hom n ≫ unitPowCollapse Y n : ι^*(M^{⊗n}) ⟶ O_Y`
(the tail common to `liftLocalHomAux` and to `powTriv`).

* `pullback_map_monoidalPowCat_powTail`: `ι^*(cat_{a,b}) ≫ powTail (a+b) = δ ≫ (powTail a ⊗ powTail b) ≫ (λ_ O).hom`
  (morphism level; the last three steps of `liftLocalHomAux_mul`).
* `powTail_app_pullbackSectionsOn_monoidalPowCat`: the same on pulled-back section pairs
  `(ι^*(cat(u ⊗ v)))|_{A'} ↦ powTail(u') • powTail(v')`.
* `liftLocalHomAux_app_pullbackSectionsOn`: `liftLocalHomAux D ι e' n` on `((ι ≫ f)^*x)|_{A'}` is `powTail n` on
  `(ι^*(Ψ_n(f^*x)))|_{A'}`.
* `liftLocalPieceAux_restrict_eq`: `liftLocalPieceAux … x` restricted to `A'` is `liftLocalHomAux` on `((ι ≫ f)^*x)|_{A'}`.

All proofs are unit tracking with `pullbackSectionsOn`
(`RestrictToLambdaBundleFamilyTransition_PullbackSections.lean`, `RelativeProjBaseChangeUnit.lean`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `(φ ≫ ψ).app U x = ψ.app U (φ.app U x)` (definitional). -/
theorem comp_app_apply_tfam {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : X.Opens) (x : Γ(M, U)) :
    (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

/-- Equal morphisms agree on sections. -/
theorem hom_congr_app_tfam {M N : X.Modules} {φ ψ : M ⟶ N} (h : φ = ψ) (U : X.Opens) (x : Γ(M, U)) :
    φ.app U x = ψ.app U x := by
  subst h
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X T Y : AlgebraicGeometry.Scheme.{u}}

section PowTail

set_option backward.isDefEq.respectTransparency.types false

/-- The tail `ι^*(M^{⊗n}) ⟶ (ι^*M)^{⊗n} ⟶ O_Y^{⊗n} ⟶ O_Y` shared by `liftLocalHomAux` and `powTriv`. -/
def powTail (ι : Y ⟶ T) (M : T.Modules)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback ι).obj (AlgebraicGeometry.Scheme.Modules.monoidalPow M n) ⟶
      𝟙_ Y.Modules :=
  AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow ι M n ≫
    AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom n ≫
    AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n

/-- **The tail is multiplicative** (morphism level): `ι^*(cat_{a,b}) ≫ powTail (a+b) = δ ≫ (powTail a ⊗ powTail b) ≫ (λ_ O).hom`
(`pullbackMonoidalPow_monoidalPowCat`, `monoidalPowCat_monoidalPowMap`, `unitPowCollapse_monoidalPowCat`; the last
three steps of `liftLocalHomAux_mul`). -/
theorem pullback_map_monoidalPowCat_powTail (ι : Y ⟶ T) (M : T.Modules)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) (a b : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback ι).map (AlgebraicGeometry.Scheme.Modules.monoidalPowCat M a b).hom ≫
        AlgebraicGeometry.Scheme.relativeProj.powTail ι M e' (a + b) =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom ι
          (AlgebraicGeometry.Scheme.Modules.monoidalPow M a) (AlgebraicGeometry.Scheme.Modules.monoidalPow M b) ≫
        (AlgebraicGeometry.Scheme.relativeProj.powTail ι M e' a ⊗ₘ
          AlgebraicGeometry.Scheme.relativeProj.powTail ι M e' b) ≫
        (λ_ (𝟙_ Y.Modules)).hom := by
  unfold AlgebraicGeometry.Scheme.relativeProj.powTail
  have h3 := AlgebraicGeometry.Scheme.Modules.pullbackMonoidalPow_monoidalPowCat_assoc ι M a b
    (AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom (a + b) ≫
      AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y (a + b))
  have h4 : (AlgebraicGeometry.Scheme.Modules.monoidalPowCat
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M) a b).hom ≫
        AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom (a + b) ≫
        AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y (a + b) =
      (AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom a ⊗ₘ
          AlgebraicGeometry.Scheme.Modules.monoidalPowMap e'.hom b) ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowCat (𝟙_ Y.Modules) a b).hom ≫
        AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y (a + b) :=
    ((reassoc_of% (AlgebraicGeometry.Scheme.Modules.monoidalPowCat_monoidalPowMap e'.hom a b)) _).symm
  have h5 := AlgebraicGeometry.Scheme.Modules.unitPowCollapse_monoidalPowCat Y a b
  rw [h3, h4, h5, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]

/-- **The tail on pulled-back section pairs**: for `u ∈ Γ(M^{⊗a}, B)`, `v ∈ Γ(M^{⊗b}, B)` and `A' ≤ ι⁻¹B`,
`powTail (a+b) ((ι^*(cat(u ⊗ v)))|_{A'}) = powTail a ((ι^*u)|_{A'}) • powTail b ((ι^*v)|_{A'})`
(the previous lemma on sections; `pullback_map_app_pullbackSectionsOn_bc`, `pullbackTensorObjHom_app_pullbackSectionsOn`,
`tensorHom_tensorSections`, `leftUnitor_app_tensorSections`). -/
theorem powTail_app_pullbackSectionsOn_monoidalPowCat (ι : Y ⟶ T) (M : T.Modules)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) (a b : ℕ)
    (B : T.Opens) (A' : Y.Opens) (h : A' ≤ ι ⁻¹ᵁ B)
    (u : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow M a, B))
    (v : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow M b, B)) :
    (show Γ(Y, A') from (AlgebraicGeometry.Scheme.relativeProj.powTail ι M e' (a + b)).app A'
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ι
          (AlgebraicGeometry.Scheme.Modules.monoidalPow M (a + b)) B A' h
          ((AlgebraicGeometry.Scheme.Modules.monoidalPowCat M a b).hom.app B
            (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ B u v)))) =
      (show Γ(Y, A') from (AlgebraicGeometry.Scheme.relativeProj.powTail ι M e' a).app A'
          (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ι
            (AlgebraicGeometry.Scheme.Modules.monoidalPow M a) B A' h u)) *
        (show Γ(Y, A') from (AlgebraicGeometry.Scheme.relativeProj.powTail ι M e' b).app A'
          (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ι
            (AlgebraicGeometry.Scheme.Modules.monoidalPow M b) B A' h v)) := by
  have hm := AlgebraicGeometry.Scheme.Modules.hom_congr_app_tfam
    (AlgebraicGeometry.Scheme.relativeProj.pullback_map_monoidalPowCat_powTail ι M e' a b) A'
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ι
      (AlgebraicGeometry.Scheme.Modules.monoidalPow M a ⊗ AlgebraicGeometry.Scheme.Modules.monoidalPow M b) B A' h
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ B u v))
  rw [AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam, AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam,
    AlgebraicGeometry.Scheme.Modules.comp_app_apply_tfam,
    AlgebraicGeometry.Scheme.Modules.pullback_map_app_pullbackSectionsOn_bc,
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_app_pullbackSectionsOn] at hm
  refine (show _ = _ from hm).trans ?_
  have ht := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
    (AlgebraicGeometry.Scheme.relativeProj.powTail ι M e' a) (AlgebraicGeometry.Scheme.relativeProj.powTail ι M e' b) A'
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ι (AlgebraicGeometry.Scheme.Modules.monoidalPow M a) B A' h u)
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ι (AlgebraicGeometry.Scheme.Modules.monoidalPow M b) B A' h v)
  refine (congrArg ((λ_ (𝟙_ Y.Modules)).hom.app A') ht).trans ?_
  exact AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections (𝟙_ Y.Modules) A' _ _

end PowTail

section LiftLocal

variable {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}

/-- `liftLocalHomAux D ι e' n = C⁻¹ ≫ ι^*Ψ_n ≫ powTail n` on the pulled-back section `((ι ≫ f)^*x)|_{A'}`:
the first two factors send it to `(ι^*(Ψ_n(f^*x)))|_{A'}` (`pullbackComp_inv_app_pullbackSectionsOn`,
`pullback_map_app_pullbackSectionsOn_bc`). -/
theorem liftLocalHomAux_app_pullbackSectionsOn (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (ι : Y ⟶ T) (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (A' : Y.Opens) (h : A' ≤ (ι ≫ f) ⁻¹ᵁ W) (h' : A' ≤ ι ⁻¹ᵁ (f ⁻¹ᵁ W)) (n : ℕ)
    (x : Γ(S.part n, W)) :
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n).app A'
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (ι ≫ f) (S.part n) W A' h x) =
      (AlgebraicGeometry.Scheme.relativeProj.powTail ι M e' n).app A'
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ι
          (AlgebraicGeometry.Scheme.Modules.monoidalPow M n) (f ⁻¹ᵁ W) A' h'
          ((D.Ψ n).app (f ⁻¹ᵁ W) (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom f (S.part n) W x))) := by
  change (AlgebraicGeometry.Scheme.relativeProj.powTail ι M e' n).app A'
    (((AlgebraicGeometry.Scheme.Modules.pullback ι).map (D.Ψ n)).app A'
      (((AlgebraicGeometry.Scheme.Modules.pullbackComp ι f).app (S.part n)).inv.app A'
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (ι ≫ f) (S.part n) W A' h x))) = _
  rw [AlgebraicGeometry.Scheme.Modules.pullbackComp_inv_app_pullbackSectionsOn ι f (S.part n) W A' h' h,
    AlgebraicGeometry.Scheme.Modules.pullback_map_app_pullbackSectionsOn_bc]

/-- `liftLocalPieceAux … x` restricted from `⊤` to `A'` is `liftLocalHomAux` on `((ι ≫ f)^*x)|_{A'}`
(`liftLocalPieceAux_apply`, `app_map`, `pullbackSectionsOn_restrict`). -/
theorem liftLocalPieceAux_restrict_eq (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)
    (ι : Y ⟶ T) (e' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (W : X.Opens) (hW : (⊤ : Y.Opens) ≤ (ι ≫ f) ⁻¹ᵁ W) (n : ℕ) (x : S.sectionsPiece W n) (A' : Y.Opens) :
    Y.presheaf.map (homOfLE (le_top : A' ≤ ⊤)).op
        (AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux D ι e' W hW n x) =
      (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n).app A'
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (ι ≫ f) (S.part n) W A' (le_top.trans hW) x) := by
  rw [AlgebraicGeometry.Scheme.relativeProj.liftLocalPieceAux_apply]
  have h1 := AlgebraicGeometry.Scheme.Modules.app_map
    (AlgebraicGeometry.Scheme.relativeProj.liftLocalHomAux D ι e' n) (le_top : A' ≤ ⊤)
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (ι ≫ f) (S.part n) W ⊤ hW x)
  have h2 := AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_restrict (ι ≫ f) (S.part n) hW
    (le_top.trans hW) (le_refl W) (le_top : A' ≤ ⊤) x
  have h3 : (S.part n).presheaf.map (homOfLE (le_refl W)).op x = x :=
    AlgebraicGeometry.Scheme.Modules.map_homOfLE_rfl (M := S.part n) W x
  rw [h3] at h2
  rw [h2] at h1
  exact h1.symm

end LiftLocal

end AlgebraicGeometry.Scheme.relativeProj

end
