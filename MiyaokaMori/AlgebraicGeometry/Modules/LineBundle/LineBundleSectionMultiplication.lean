import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesUnitHomTopSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Multiplication by a global section

The map "multiplication by a global section": `s ∈ Γ(X, L ⊗ N^{-1})` gives `·s : N → L`
(`N ≅ N ⊗ O →(N ◁ σ_s) N ⊗ (L ⊗ N^∨) ≅ L ⊗ (N ⊗ N^∨) →(contraction) L`), and `s ↦ ·s` is injective.
Used for the sequence `0 → N →(·s) L`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- The map `·s : N → L` of multiplication by a section `s ∈ Γ(X, L ⊗ N^{-1})`, given entirely by constructions:
   `N ≅ N ⊗ O_X →(N ◁ σ_s) N ⊗ (L ⊗ N^{-1}) ≅ N ⊗ (L ⊗ N^∨) ≅ (N ⊗ L) ⊗ N^∨ →(braiding) (L ⊗ N) ⊗ N^∨ ≅ L ⊗ (N ⊗ N^∨) →(contraction) L ⊗ O_X ≅ L`,
   where `σ_s : O_X → L ⊗ N^{-1}` is the morphism corresponding to `s` (`homOfTopSection`), `Modules.tensor`
   and `⊗` are exchanged through `tensorIsoTensorObj`, `N^{-1} ≅ N^∨` is `zpowNegOneIso`, and the contraction
   is the forward direction of `LineBundle.contraction` (braiding followed by evaluation). -/

noncomputable def LineBundle.mulBySection {k : Type u} [Field k] {X : Variety k} (N L : LineBundle X)
    (s : ((L.tensor (N.zpow (-1))).toModules.val.obj (Opposite.op ⊤) : Type u)) :
    N.toModules ⟶ L.toModules :=
  (ρ_ N.toModules).inv ≫
    N.toModules ◁ ((show 𝟙_ X.toScheme.Modules ⟶ (L.tensor (N.zpow (-1))).toModules from
        AlgebraicGeometry.Scheme.Modules.homOfTopSection _ s) ≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L.toModules (N.zpow (-1)).toModules).hom ≫
      L.toModules ◁ N.zpowNegOneIso.hom) ≫
    (α_ N.toModules L.toModules (AlgebraicGeometry.Scheme.Modules.dual N.toModules)).inv ≫
    (β_ N.toModules L.toModules).hom ▷ AlgebraicGeometry.Scheme.Modules.dual N.toModules ≫
    (α_ L.toModules N.toModules (AlgebraicGeometry.Scheme.Modules.dual N.toModules)).hom ≫
    L.toModules ◁ N.contraction.hom ≫
    (ρ_ L.toModules).hom

/- Sanity check: `s ↦ ·s` is injective (`Hom(N, L) ≅ Γ(X, L ⊗ N^{-1})`); in particular `·s = 0` iff `s = 0`. -/

theorem LineBundle.mulBySection_injective {k : Type u} [Field k] {X : Variety k} (N L : LineBundle X) :
    Function.Injective (LineBundle.mulBySection N L) := by
  intro s t h
  let fs : (𝟙_ X.toScheme.Modules) ⟶ (L.tensor (N.zpow (-1))).toModules :=
    AlgebraicGeometry.Scheme.Modules.homOfTopSection _ s
  let ft : (𝟙_ X.toScheme.Modules) ⟶ (L.tensor (N.zpow (-1))).toModules :=
    AlgebraicGeometry.Scheme.Modules.homOfTopSection _ t
  let e : (L.tensor (N.zpow (-1))).toModules ⟶
      L.toModules ⊗ AlgebraicGeometry.Scheme.Modules.dual N.toModules :=
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      L.toModules (N.zpow (-1)).toModules).hom ≫
      L.toModules ◁ N.zpowNegOneIso.hom
  let eIso : (L.tensor (N.zpow (-1))).toModules ≅
      L.toModules ⊗ AlgebraicGeometry.Scheme.Modules.dual N.toModules :=
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      L.toModules (N.zpow (-1)).toModules ≪≫
      CategoryTheory.MonoidalCategory.whiskerLeftIso L.toModules N.zpowNegOneIso
  have hcomp : N.toModules ◁ (fs ≫ e) = N.toModules ◁ (ft ≫ e) := by
    simpa only [LineBundle.mulBySection, fs, ft, e, cancel_epi, cancel_mono] using h
  have he : e = eIso.hom := rfl
  haveI : IsIso e := he.symm ▸ eIso.isIso_hom
  have hleft : N.toModules ◁ fs = N.toModules ◁ ft := by
    apply (cancel_mono (N.toModules ◁ e)).mp
    simpa only [← CategoryTheory.MonoidalCategory.whiskerLeft_comp] using hcomp
  haveI : (CategoryTheory.MonoidalCategory.tensorRight N.toModules).IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle N.toModules
  have hhom : fs = ft := by
    apply (CategoryTheory.MonoidalCategory.tensorRight N.toModules).map_injective
    change fs ▷ N.toModules = ft ▷ N.toModules
    rw [← cancel_epi (CategoryTheory.BraidedCategory.braiding N.toModules _).hom]
    simpa using congrArg
      (fun f ↦ f ≫ (CategoryTheory.BraidedCategory.braiding N.toModules
        (L.tensor (N.zpow (-1))).toModules).hom) hleft
  refine (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop
    (L.tensor (N.zpow (-1))).toModules).symm.injective ?_
  change fs = ft
  exact hhom

end
