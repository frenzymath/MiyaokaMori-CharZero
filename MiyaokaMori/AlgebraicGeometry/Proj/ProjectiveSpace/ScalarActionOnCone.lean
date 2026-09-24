import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesPowLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.ScalarActionOnConeHomogeneousPullback
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ConeScalingActionIdealSheafOfSectionLeKer

/-! # The scalar action on the twisted affine cone

The `G_m`-action `λ·(z_0,…,z_N) = (λz_0,…,λz_N)` on the twisted affine cone: since the `F_j` are
homogeneous it preserves `Z`, and it is an action over `C`.

Reference: Definition 2.1 of the paper (the twisted affine cone).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The data of `coneScalarAction` (the `C`-structure of `P = A¹_k ×_k Z`, the section `z`, the scaled
   section `λ·z`, and the factorization through `toImage ≫ inclusion`) and its two proof obligations
   (compatibility for `Over.homMk`, and `I ≤ ker g`) are stated separately below. -/

/-- The ideal sheaf `I = ⨆_j (ideal sheaf of F_j = 0)` of the cone. -/

noncomputable abbrev coneScalarAction.ideal {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left.IdealSheafData :=
  (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection (k := k) A N (F j) (hF j)))

/-- `P = A¹_k ×_k Z` as a `C`-scheme: `P → Z → C`. -/

noncomputable abbrev coneScalarAction.toBase {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    (CategoryTheory.Limits.pullback
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) ⟶ C :=
  CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ (twistedAffineCone A N deg F hF).hom

/-- `P → Z ⊆ Tot(V)` is over `C` (the compatibility for `Over.homMk`): `Z → Tot(V) → C` is the
structure morphism of `Z`. -/
theorem coneScalarAction.point_compat {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    (CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
          (coneScalarAction.ideal A N deg F hF).subschemeι) ≫
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom =
      (CategoryTheory.Over.mk (coneScalarAction.toBase A N deg F hF)).hom :=
  CategoryTheory.Category.assoc _ _ _

/-- The scaled `T`-point `λ·z : P → Tot(V)` (Yoneda, the inverse of `totalSpaceHomEquiv`). -/

noncomputable def coneScalarAction.scaledTot {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    (CategoryTheory.Limits.pullback
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left :=
  let t := coneScalarAction.toBase A N deg F hF
  let z := AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk t)
    (CategoryTheory.Over.homMk (CategoryTheory.Limits.pullback.snd (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
        (coneScalarAction.ideal A N deg F hF).subschemeι)
      (coneScalarAction.point_compat A N deg F hF))
  ((AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk t)).symm
    (@HSMul.hSMul ((CategoryTheory.Limits.pullback
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).ringCatSheaf.val.obj (Opposite.op ⊤))
      (((AlgebraicGeometry.Scheme.Modules.pullback t).obj (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).val.obj (Opposite.op ⊤))
      (((AlgebraicGeometry.Scheme.Modules.pullback t).obj (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).val.obj (Opposite.op ⊤)) _
      ((CategoryTheory.Limits.pullback.fst (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom Polynomial.X)) z)).left

/-- Homogeneity of `F_j`: `F_j(λz) = λ^{d_j} F_j(z) = 0`, hence `I ≤ ker(λ·z)`.

Proof sketch: after `iSup_le`, the criterion `idealSheafOfSection_le_ker_iff` reduces the claim to
"the pullback of `F_j(τ)` along `λ·z` vanishes"; this is the core lemma
`homogeneousEquationSection_pullback_eq_zero_of_coordinates_smul` with `S = P`, `b = t`,
`j₀ = pr₂ ≫ ι_Z`, `j = λ·z`, `a = λ`. The coordinate hypothesis `(λ·z)_i = λ • z_i` is
`totalSpaceHomEquiv_symm_smul_coordinate`, and `j₀^*F_j(τ) = 0` follows from
`I_j ≤ I = ker ι_Z ≤ ker(pr₂ ≫ ι_Z)` (`ker_subschemeι`, `Hom.le_ker_comp`) and the forward
direction of the criterion. -/
theorem coneScalarAction.ideal_le_ker_scaledTot {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    coneScalarAction.ideal A N deg F hF ≤ (coneScalarAction.scaledTot A N deg F hF).ker := by
  refine iSup_le (fun j => ?_)
  rw [AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff]
  let t := coneScalarAction.toBase A N deg F hF
  let g₀ := CategoryTheory.Limits.pullback.snd
      (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
    (coneScalarAction.ideal A N deg F hF).subschemeι
  let m₀ : CategoryTheory.Over.mk t ⟶
      AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) :=
    CategoryTheory.Over.homMk g₀ (coneScalarAction.point_compat A N deg F hF)
  let z := AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
    (CategoryTheory.Over.mk t) m₀
  let lam : Γ(CategoryTheory.Limits.pullback
      (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))), ⊤) :=
    (CategoryTheory.Limits.pullback.fst
      (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom Polynomial.X)
  let m : CategoryTheory.Over.mk t ⟶
      AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) :=
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
      (CategoryTheory.Over.mk t)).symm
      ((show (CategoryTheory.Limits.pullback
          (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          ((twistedAffineCone A N deg F hF).hom ≫
            (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).ringCatSheaf.obj.obj (Opposite.op ⊤) from lam) • z)
  have hb : coneScalarAction.scaledTot A N deg F hF ≫
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = t :=
    CategoryTheory.Over.w m
  have hb₀ : g₀ ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = t :=
    coneScalarAction.point_compat A N deg F hF
  have hm : (CategoryTheory.Over.homMk (coneScalarAction.scaledTot A N deg F hF) hb :
      CategoryTheory.Over.mk t ⟶
        AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))) = m :=
    CategoryTheory.Over.OverMorphism.ext rfl
  have hcoord : ∀ i : Fin (N + 1),
      (((AlgebraicGeometry.Scheme.Modules.pullback t).map
          (biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
            (CategoryTheory.Over.mk t)
            (CategoryTheory.Over.homMk (coneScalarAction.scaledTot A N deg F hF) hb))
        = (show (CategoryTheory.Limits.pullback
            (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            ((twistedAffineCone A N deg F hF).hom ≫
              (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).ringCatSheaf.obj.obj (Opposite.op ⊤) from lam) •
          (((AlgebraicGeometry.Scheme.Modules.pullback t).map
            (biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
            (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
              (CategoryTheory.Over.mk t) (CategoryTheory.Over.homMk g₀ hb₀)) := by
    intro i
    rw [hm]
    exact AlgebraicGeometry.Scheme.totalSpaceHomEquiv_symm_smul_coordinate (fun _ : Fin (N + 1) => A)
      (CategoryTheory.Over.mk t) lam z i
  have h₀ : sectionPullbackAlong g₀ (homogeneousEquationSection A N (F j) (hF j)) = 0 := by
    rw [← AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff]
    exact (le_iSup (fun j => AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection (k := k) A N (F j) (hF j))) j).trans
      ((coneScalarAction.ideal A N deg F hF).ker_subschemeι.symm.le.trans
        (AlgebraicGeometry.Scheme.Hom.le_ker_comp _ _))
  exact homogeneousEquationSection_pullback_eq_zero_of_coordinates_smul A N (F j) (hF j) t g₀
    (coneScalarAction.scaledTot A N deg F hF) hb₀ hb lam hcoord h₀

noncomputable def coneScalarAction {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    (CategoryTheory.Limits.pullback
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        ((twistedAffineCone A N deg F hF).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) ⟶
      (twistedAffineCone A N deg F hF).left :=
  (coneScalarAction.scaledTot A N deg F hF).toImage ≫
    AlgebraicGeometry.Scheme.IdealSheafData.inclusion (coneScalarAction.ideal_le_ker_scaledTot A N deg F hF)

-- The action is compatible with the structure morphism (`λ·z` and `z` lie over the same point of `C`).

theorem coneScalarAction_comp {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j)) :
    coneScalarAction A N deg F hF ≫ (twistedAffineCone A N deg F hF).hom =
      CategoryTheory.Limits.pullback.snd _ _ ≫ (twistedAffineCone A N deg F hF).hom := by
  have h : coneScalarAction A N deg F hF ≫ (coneScalarAction.ideal A N deg F hF).subschemeι =
      coneScalarAction.scaledTot A N deg F hF :=
    calc coneScalarAction A N deg F hF ≫ (coneScalarAction.ideal A N deg F hF).subschemeι
        = (coneScalarAction.scaledTot A N deg F hF).toImage ≫
            (AlgebraicGeometry.Scheme.IdealSheafData.inclusion
              (coneScalarAction.ideal_le_ker_scaledTot A N deg F hF) ≫
              (coneScalarAction.ideal A N deg F hF).subschemeι) := CategoryTheory.Category.assoc _ _ _
      _ = (coneScalarAction.scaledTot A N deg F hF).toImage ≫
            (coneScalarAction.scaledTot A N deg F hF).ker.subschemeι := by
          rw [AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι]
      _ = coneScalarAction.scaledTot A N deg F hF := AlgebraicGeometry.Scheme.Hom.toImage_imageι _
  calc coneScalarAction A N deg F hF ≫ (twistedAffineCone A N deg F hF).hom
      = (coneScalarAction A N deg F hF ≫ (coneScalarAction.ideal A N deg F hF).subschemeι) ≫
          (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom :=
        (CategoryTheory.Category.assoc _ _ _).symm
    _ = coneScalarAction.scaledTot A N deg F hF ≫
          (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom :=
        congrArg (fun φ => φ ≫
          (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom) h
    _ = CategoryTheory.Limits.pullback.snd _ _ ≫ (twistedAffineCone A N deg F hF).hom :=
        CategoryTheory.Over.w _

end
