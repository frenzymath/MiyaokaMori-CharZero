import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Frames
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Basis
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_RelSpecOverBase

/-! # The jet chart trivialization

A frame `ε` of `L` on an affine open `V` gives an isomorphism of `V`-schemes
`C̃_(κ)(L)|_V ≅ Spec(O(V)[t]/(t^{κ+1}))`, where `t` corresponds to the dual frame `ε^∨ ∈ L^{-1}(V)`
(§3 of the paper: "a frame ε of L on V identifies C̃_(κ)(L)|_V with Spec(O(V)[t]/(t^{κ+1}))").

**Proof.** Write `𝒜 := truncatedJetAlgebra L κ` (`𝒜 = ⊕_{q ≤ κ} L^{-q}`),
`D := L^∨ = Modules.dual L`, `M := (L.zpow (-1)).toModules`.
1. `ε` is a frame of `L` on `V` (`LineBundle.Frame.isFrame`), so it has a dual frame `δ ∈ Γ(V, D)` with `⟨δ, ε⟩ = 1`
   (`IsFrame.exists_dual_pairing_one_dualEv`; the pairing is `dualEv L`, definitionally `internalHomEval L O`), and `δ` is a frame of
   `D` (`IsFrame.dual_of_pairing_eq_one`); `μ := zpowNegOneIso⁻¹(δ)` is a frame of `M` (`IsFrame.map_iso`).
2. `𝒜(V)` is the free `O(V)`-module on `τ_q = ι_q(μ^{⊗q})`, `q ≤ κ`, with `τ_a τ_b = τ_{a+b}` (or `0` above `κ`), so
   `O(V)[t]/(t^{κ+1}) → 𝒜(V)`, `t ↦ τ_1` (`0` if `κ = 0`), is a ring isomorphism over `O(V)`
   (`truncatedJetAlgebra.quotToSections_bijective`, `_comp_mk_comp_C`, `_mk_X`; module `JetChartTrivialization_Basis`).
3. `e := affineIso 𝒜 V ≪≫ Spec(that isomorphism)`. It is over `V` because `affineIso.hom ≫ Spec(sectionsUnit) =
   (p_L ∣_ V) ≫ isoSpec.hom` (`relativeSpec.affineIso_hom_Spec_map_sectionsUnit`) and the ring isomorphism carries
   the constants to `sectionsUnit`. The coordinate `t` pulls back, via `ΓSpecIso_inv_naturality`, to the image of
   `τ_1 = ι_1(1 ⊗ μ) = ι_1((𝟙 ◁ zpowNegOneIso⁻¹)((λ_ D)⁻¹ δ))` under `affineIso`, which is the third clause.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- The frame `ε` identifies `C̃_(κ)(L)|_V` with `Spec(O(V)[t]/(t^{κ+1}))`. Three conclusions:
   (1) the isomorphism `e`; (2) `e` is an isomorphism over `V`: `e` followed by `Spec` of `O(V) → O(V)[t]/(t^{κ+1})`
   equals `p_L|_V` followed by `V ≅ Spec O(V)`; (3) the relation between `ε` and `t`: `t` corresponds to the dual
   frame `ε^∨ ∈ L^{-1}(V)`. Here `ε^∨` is the section `δ` of `L^∨ = 𝓗om(L, O)` on `V` with `⟨δ, ε⟩ = 1` (unique,
   since `L` is a line bundle and `ε` a frame); it is sent through `L^∨ ≅ 𝟙 ⊗ L^∨ ≅ 𝟙 ⊗ L^{-1}` = the first piece
   (`zpowNegOneIso`) and the inclusion of the first piece into `𝒜(V) = ⊕_{q≤κ} L^{-q}(V)`, then viewed as a
   function on `p_L⁻¹V` via `relativeSpec.affineIso` (`p_L⁻¹V ≅ Spec 𝒜(V)`). For `κ = 0` there is no weight-`1`
   piece and `t = 0`, so (3) carries the hypothesis `1 ≤ κ`. -/

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem jetNeighborhood.trivialization_of_frame {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ)
    {V : Ct.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    (ε : LineBundle.Frame L V) :
    ∃ e : ((jetNeighborhood.proj L κ) ⁻¹ᵁ V).toScheme ≅
        AlgebraicGeometry.Spec (CommRingCat.of
          (Polynomial Γ(Ct.toScheme, V) ⧸
            Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)})),
      e.hom ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)})).comp
            Polynomial.C)) =
        (jetNeighborhood.proj L κ ∣_ V) ≫ hV.isoSpec.hom ∧
      ∀ hκ : 1 ≤ κ,
        ∃ δ : ((AlgebraicGeometry.Scheme.Modules.dual L.toModules).val.obj (Opposite.op V) : Type u),
          ((AlgebraicGeometry.Scheme.Modules.internalHomEval L.toModules
                (SheafOfModules.unit Ct.toScheme.ringCatSheaf)).val.app (Opposite.op V)).hom
              (AlgebraicGeometry.Scheme.Modules.tensorSections
                (AlgebraicGeometry.Scheme.Modules.dual L.toModules) L.toModules V δ ε.section_)
            = (1 : Ct.toScheme.ringCatSheaf.obj.obj (Opposite.op V)) ∧
          e.hom.appTop.hom ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv.hom
              (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)})
                Polynomial.X)) =
            (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) ⟨V, hV⟩).hom.appTop.hom
              ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv.hom
                (show (truncatedJetAlgebra L κ).sectionsRing V from
                  (((λ_ (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).inv ≫
                      ((𝟙_ Ct.toScheme.Modules) ◁ L.zpowNegOneIso.inv) ≫
                      CategoryTheory.Limits.biproduct.ι
                        (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
                        ⟨1, Nat.lt_succ_of_le hκ⟩).val.app (Opposite.op V)).hom δ)) := by
  classical
  -- Step 1: the dual frame `δ` and the frame `μ := zpowNegOneIso⁻¹(δ)` of `L^{-1}`
  have hε : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules V ε.section_ := ε.isFrame
  refine hε.exists_dual_pairing_one_dualEv.elim fun δ hK => ?_
  have hδ : AlgebraicGeometry.Scheme.Modules.IsFrame (AlgebraicGeometry.Scheme.Modules.dual L.toModules) V δ :=
    AlgebraicGeometry.Scheme.Modules.IsFrame.dual_of_pairing_eq_one hK
  have hμ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules V (L.zpowNegOneIso.inv.app V δ) :=
    hδ.map_iso L.zpowNegOneIso.symm
  -- Step 2: the ring isomorphism `O(V)[t]/(t^{κ+1}) ≅ 𝒜(V)`
  have hφ := truncatedJetAlgebra.quotToSections_bijective L V (L.zpowNegOneIso.inv.app V δ) κ hμ
  haveI : CategoryTheory.IsIso (CommRingCat.ofHom
      (truncatedJetAlgebra.quotToSections L V (L.zpowNegOneIso.inv.app V δ) κ)) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr hφ
  -- Step 3: the scheme isomorphism
  refine ⟨AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) (⟨V, hV⟩ : Ct.toScheme.affineOpens) ≪≫
    CategoryTheory.asIso (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (truncatedJetAlgebra.quotToSections L V (L.zpowNegOneIso.inv.app V δ) κ))), ?_, ?_⟩
  · -- over `V`
    have h1 : AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (truncatedJetAlgebra.quotToSections L V (L.zpowNegOneIso.inv.app V δ) κ)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          ((Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)})).comp
            Polynomial.C)) =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((truncatedJetAlgebra L κ).sectionsUnit V)) :=
      (AlgebraicGeometry.Spec.map_comp _ _).symm.trans (congrArg AlgebraicGeometry.Spec.map
        ((CommRingCat.ofHom_comp _ _).symm.trans
          (congrArg CommRingCat.ofHom (truncatedJetAlgebra.quotToSections_comp_mk_comp_C L V _ κ))))
    show (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) (⟨V, hV⟩ : Ct.toScheme.affineOpens)).hom ≫
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (truncatedJetAlgebra.quotToSections L V (L.zpowNegOneIso.inv.app V δ) κ)) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)})).comp
          Polynomial.C))) = _
    exact (congrArg (fun m => (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) (⟨V, hV⟩ : Ct.toScheme.affineOpens)).hom ≫ m)
      h1).trans
      (AlgebraicGeometry.Scheme.relativeSpec.affineIso_hom_Spec_map_sectionsUnit (truncatedJetAlgebra L κ) (⟨V, hV⟩ : Ct.toScheme.affineOpens))
  · intro hκ
    refine ⟨δ, hK, ?_⟩
    show (AlgebraicGeometry.Scheme.relativeSpec.affineIso (truncatedJetAlgebra L κ) (⟨V, hV⟩ : Ct.toScheme.affineOpens)).hom.appTop.hom
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (truncatedJetAlgebra.quotToSections L V (L.zpowNegOneIso.inv.app V δ) κ))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv.hom
          (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)}) Polynomial.X))) = _
    congr 1
    have hnat : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (truncatedJetAlgebra.quotToSections L V (L.zpowNegOneIso.inv.app V δ) κ))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv.hom
          (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)}) Polynomial.X)) =
        (AlgebraicGeometry.Scheme.ΓSpecIso _).inv.hom
          (truncatedJetAlgebra.quotToSections L V (L.zpowNegOneIso.inv.app V δ) κ
            (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)}) Polynomial.X)) :=
      (congrArg (fun g => g.hom
          (Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial Γ(Ct.toScheme, V)) ^ (κ + 1)}) Polynomial.X))
        (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (truncatedJetAlgebra.quotToSections L V (L.zpowNegOneIso.inv.app V δ) κ)))).symm
    refine hnat.trans ?_
    congr 1
    refine ((truncatedJetAlgebra.quotToSections_mk_X L V _ κ).trans
      (truncatedJetAlgebra.tau'_of_le L V _ κ hκ)).trans ?_
    show (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨1, Nat.lt_succ_of_le hκ⟩).app V (truncatedJetAlgebra.framePow L V (L.zpowNegOneIso.inv.app V δ) 1) =
      (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨1, Nat.lt_succ_of_le hκ⟩).app V
        (((𝟙_ Ct.toScheme.Modules) ◁ L.zpowNegOneIso.inv).app V
          ((λ_ (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).inv.app V δ))
    refine congrArg _ ?_
    exact ((congrArg (((𝟙_ Ct.toScheme.Modules) ◁ L.zpowNegOneIso.inv).app V)
      (AlgebraicGeometry.Scheme.Modules.leftUnitor_inv_app_jct _ V δ)).trans
      (AlgebraicGeometry.Scheme.Modules.whiskerLeft_app_tensorSections_jct _ L.zpowNegOneIso.inv V _ δ)).symm

end
