import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyMonoidalPow
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence

/-! # The multiplication map from a tensor power to the structure sheaf

For a sheaf of modules `L` on `Y` and a morphism `ι : L ⟶ O_Y`, the "multiplication" map
`powToUnit ι n : L^{⊗n} ⟶ O_Y` (the `n`-fold tensor power `monoidalPowMap ι n` of `ι` followed by the
collapse `O_Y^{⊗n} ⟶ O_Y`, then `𝟙_ Y.Modules ≅ O_Y`). Two facts about it:

* **monomorphism** (`powToUnit_mono`): if `L` is a line bundle and `ι` is a monomorphism, so is
  `powToUnit ι n`. Proof: `- ⊗ L` is an equivalence of `Y.Modules`
  (`isEquivalence_tensorRight_of_isLineBundle`), so it preserves
  monomorphisms; `P ◁ ι` is a monomorphism whenever `P ≅ 𝟙_` (`mono_whiskerLeft_of_iso_unit`), and
  `O_Y^{⊗n} ≅ 𝟙_` via `unitPowCollapse`; induction on `n` with
  `tensorHom_def : f ⊗ₘ g = (f ▷ _) ≫ (_ ◁ g)`; finally `unitPowCollapse ≫ monoidalUnitIso.hom` is an isomorphism.
* **sections** (`powToUnit_app_tensorSections`, `powToUnit_app_mPow`): on a pure tensor
  `s ⊗ e` it multiplies, `powToUnit ι (n+1) (s ⊗ e) = powToUnit ι n (s) · ι(e)`; hence on the pure tensor power
  `mPow e n = e ⊗ ⋯ ⊗ e` it gives `ι(e)ⁿ`, and every `r · ι(e)ⁿ` is in its image on sections
  (`exists_powToUnit_app_eq`).

For an ideal sheaf `J` with inclusion `ι = idealIncl J`, `powToUnit ι n` is `J.monoidalPowToUnit n`
(`Stacks0806_ReesLiftMaps`, by `rfl`); this module is stated for general `(L, ι)` so that it can sit
upstream of that definition.

Source: Stacks 01WQ (an invertible ideal sheaf is a line bundle, `J^{⊗n} ≅ Jⁿ`), 0806 (the identification
`J^{⊗n} = Jⁿ` in the construction of the lift to the blowup). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- In a monoidal category, whiskering a monomorphism `g` on the left by an object isomorphic to the unit
gives a monomorphism: `P ◁ g` followed by the isomorphism `(e.hom ▷ B) ≫ (λ_ B).hom` is
`(e.hom ▷ A) ≫ (λ_ A).hom ≫ g` (`whisker_exchange`, `leftUnitor_naturality`), a monomorphism. -/
theorem CategoryTheory.MonoidalCategory.mono_whiskerLeft_of_iso_unit {C : Type u} [Category.{v} C]
    [MonoidalCategory C] {P A B : C} (e : P ≅ 𝟙_ C) (g : A ⟶ B) [Mono g] : Mono (P ◁ g) := by
  have h : (P ◁ g) ≫ (e.hom ▷ B) ≫ (λ_ B).hom = (e.hom ▷ A) ≫ (λ_ A).hom ≫ g := by
    rw [← Category.assoc, MonoidalCategory.whisker_exchange, Category.assoc,
      MonoidalCategory.leftUnitor_naturality]
  have : Mono ((P ◁ g) ≫ (e.hom ▷ B) ≫ (λ_ B).hom) := by
    rw [h]; infer_instance
  exact mono_of_mono (P ◁ g) ((e.hom ▷ B) ≫ (λ_ B).hom)

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : AlgebraicGeometry.Scheme.{u}}

/-- `unitPowCollapse Y n : 𝟙_^{⊗n} ⟶ 𝟙_` is an isomorphism (a composite of unitors and their whiskerings).
Private copy of `isIso_unitPowCollapse` (`RelativeProjLiftMapIrrelevant`, which sits downstream of the
relative-Proj machinery and is too heavy to import here). Not a global instance. -/
private theorem isIso_unitPowCollapse_aux (n : ℕ) :
    IsIso (AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n) := by
  induction n with
  | zero => exact inferInstanceAs (IsIso (𝟙 _))
  | succ n ih =>
    change IsIso ((AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n ▷ 𝟙_ Y.Modules) ≫
      (λ_ (𝟙_ Y.Modules)).hom)
    infer_instance

/-- `L^{⊗n} ⟶ O_Y`: the `n`-fold tensor power of `ι : L ⟶ O_Y` followed by the collapse `O_Y^{⊗n} ⟶ O_Y`
(`unitPowCollapse`) and `𝟙_ Y.Modules ≅ O_Y` (`monoidalUnitIso`). On a pure tensor `e₁ ⊗ ⋯ ⊗ eₙ` it is the
product `ι(e₁)⋯ι(eₙ)`. -/
noncomputable def powToUnit {L : Y.Modules} (ι : L ⟶ SheafOfModules.unit Y.ringCatSheaf) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.monoidalPow L n ⟶ SheafOfModules.unit Y.ringCatSheaf :=
  AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n ≫
    AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n ≫
    (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).hom

/-- The tensor power `ι^{⊗n} : L^{⊗n} ⟶ O_Y^{⊗n}` of a monomorphism out of a line bundle is a monomorphism. -/
theorem mono_monoidalPowMap_of_isLineBundle {L : Y.Modules} [L.IsLineBundle]
    (ι : L ⟶ SheafOfModules.unit Y.ringCatSheaf) [Mono ι] (n : ℕ) :
    Mono (AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Mono (𝟙 _))
  | succ n ih =>
    haveI := AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle L
    haveI : Mono (AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n ▷ L) :=
      (CategoryTheory.MonoidalCategory.tensorRight L).map_mono
        (AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n)
    haveI := AlgebraicGeometry.Scheme.Modules.isIso_unitPowCollapse_aux (Y := Y) n
    haveI : Mono (AlgebraicGeometry.Scheme.Modules.monoidalPow (SheafOfModules.unit Y.ringCatSheaf) n ◁ ι) :=
      CategoryTheory.MonoidalCategory.mono_whiskerLeft_of_iso_unit
        (asIso (AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n)) ι
    have key : Mono ((AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n ▷ L) ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPow (SheafOfModules.unit Y.ringCatSheaf) n ◁ ι)) :=
      inferInstance
    have e : AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι (n + 1) =
        (AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n ▷ L) ≫
          (AlgebraicGeometry.Scheme.Modules.monoidalPow (SheafOfModules.unit Y.ringCatSheaf) n ◁ ι) :=
      MonoidalCategory.tensorHom_def _ _
    rw [e]
    exact key

/-- **`powToUnit ι n` is a monomorphism** when `L` is a line bundle and `ι` is a monomorphism. -/
theorem powToUnit_mono {L : Y.Modules} [L.IsLineBundle] (ι : L ⟶ SheafOfModules.unit Y.ringCatSheaf)
    [Mono ι] (n : ℕ) : Mono (AlgebraicGeometry.Scheme.Modules.powToUnit ι n) := by
  haveI := AlgebraicGeometry.Scheme.Modules.mono_monoidalPowMap_of_isLineBundle ι n
  haveI := AlgebraicGeometry.Scheme.Modules.isIso_unitPowCollapse_aux (Y := Y) n
  unfold AlgebraicGeometry.Scheme.Modules.powToUnit
  infer_instance

/-! ### Sections -/

/-- The unit isomorphism `𝟙_ Y.Modules ≅ O_Y` is the identity on sections (it is `eqToIso` of a definitional
equality; cf. `monoidalUnitIso_hom_app` in `BlowupIsoAwayFromCenterAffineLeaf`). -/
theorem monoidalUnitIso_hom_app' (W : Y.Opens) (x : Γ(𝟙_ Y.Modules, W)) :
    ((AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).hom.app W x : Γ(Y, W)) = x := by
  with_unfolding_all rfl

/-- The scalar action of `Γ(Y, W)` on `Γ(𝟙_ Y.Modules, W)` is the ring multiplication. -/
theorem smul_monoidalUnit_eq_mul' (W : Y.Opens) (r : Γ(Y, W)) (a : Γ(𝟙_ Y.Modules, W)) :
    ((r • a : Γ(𝟙_ Y.Modules, W)) : Γ(Y, W)) = r * (show Γ(Y, W) from a) := by
  with_unfolding_all rfl

/-- Right whiskering on a pure tensor: `(f ▷ C)(a ⊗ c) = f a ⊗ c` (private copy of the library lemma
`whiskerRight_app_tensorSections`, which lives downstream). -/
private theorem whiskerRight_app_tensorSections_aux {A A' : Y.Modules} (f : A ⟶ A') (C : Y.Modules)
    (W : Y.Opens) (a : Γ(A, W)) (c : Γ(C, W)) :
    (f ▷ C).app W (AlgebraicGeometry.Scheme.Modules.tensorSections A C W a c) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' C W (f.app W a) c := by
  rw [← CategoryTheory.MonoidalCategory.tensorHom_id]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections f (𝟙 C) W a c

/-- **`powToUnit` on a pure tensor multiplies**: `powToUnit ι (n+1) (s ⊗ e) = powToUnit ι n (s) · ι(e)`. -/
theorem powToUnit_app_tensorSections {L : Y.Modules} (ι : L ⟶ SheafOfModules.unit Y.ringCatSheaf) (n : ℕ)
    (W : Y.Opens) (s : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow L n, W)) (e : Γ(L, W)) :
    (AlgebraicGeometry.Scheme.Modules.powToUnit ι (n + 1)).app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections
          (AlgebraicGeometry.Scheme.Modules.monoidalPow L n) L W s e) =
      (show Γ(Y, W) from (AlgebraicGeometry.Scheme.Modules.powToUnit ι n).app W s) *
        (show Γ(Y, W) from ι.app W e) := by
  -- unfold the recursion
  have h1 : (AlgebraicGeometry.Scheme.Modules.powToUnit ι (n + 1)).app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections
          (AlgebraicGeometry.Scheme.Modules.monoidalPow L n) L W s e) =
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).hom.app W
        ((λ_ (𝟙_ Y.Modules)).hom.app W
          ((AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n ▷ 𝟙_ Y.Modules).app W
            ((AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n ⊗ₘ ι).app W
              (AlgebraicGeometry.Scheme.Modules.tensorSections
                (AlgebraicGeometry.Scheme.Modules.monoidalPow L n) L W s e)))) := rfl
  have h2 : (AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n ⊗ₘ ι).app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections
          (AlgebraicGeometry.Scheme.Modules.monoidalPow L n) L W s e) =
      AlgebraicGeometry.Scheme.Modules.tensorSections _ _ W
        ((AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n).app W s) (ι.app W e) :=
    AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections _ _ W s e
  have h3 := AlgebraicGeometry.Scheme.Modules.whiskerRight_app_tensorSections_aux
    (AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n) (𝟙_ Y.Modules) W
    ((AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n).app W s) (ι.app W e)
  have h4 := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections (𝟙_ Y.Modules) W
    (show Γ(Y, W) from (AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n).app W
      ((AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n).app W s)) (ι.app W e)
  have h5 : (show Γ(Y, W) from (AlgebraicGeometry.Scheme.Modules.powToUnit ι n).app W s) =
      (show Γ(Y, W) from (AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n).app W
        ((AlgebraicGeometry.Scheme.Modules.monoidalPowMap ι n).app W s)) :=
    AlgebraicGeometry.Scheme.Modules.monoidalUnitIso_hom_app' W _
  refine h1.trans ?_
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).hom.app W
    ((λ_ (𝟙_ Y.Modules)).hom.app W
      ((AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n ▷ 𝟙_ Y.Modules).app W z))) h2).trans ?_
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).hom.app W
    ((λ_ (𝟙_ Y.Modules)).hom.app W z)) h3).trans ?_
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).hom.app W z)
    h4).trans ?_
  rw [AlgebraicGeometry.Scheme.Modules.monoidalUnitIso_hom_app',
    AlgebraicGeometry.Scheme.Modules.smul_monoidalUnit_eq_mul', h5]

/-- `powToUnit ι 0` is the unit identification `𝟙_ Y.Modules ≅ O_Y`. -/
theorem powToUnit_zero {L : Y.Modules} (ι : L ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    AlgebraicGeometry.Scheme.Modules.powToUnit ι 0 =
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).hom := by
  show 𝟙 _ ≫ 𝟙 _ ≫ _ = _
  simp

/-- The pure tensor power `e ⊗ ⋯ ⊗ e ∈ Γ(L^{⊗n}, W)` of a section `e ∈ Γ(L, W)`
(`mPow e 0 = 1`, `mPow e (n+1) = mPow e n ⊗ e`; the `monoidalPow` analogue of `framePow`). -/
def mPow {L : Y.Modules} {W : Y.Opens} (e : Γ(L, W)) :
    (n : ℕ) → Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow L n, W)
  | 0 => (1 : Γ(Y, W))
  | n + 1 => AlgebraicGeometry.Scheme.Modules.tensorSections
      (AlgebraicGeometry.Scheme.Modules.monoidalPow L n) L W (AlgebraicGeometry.Scheme.Modules.mPow e n) e

/-- **`powToUnit` on a pure tensor power is the power of `ι(e)`**: `powToUnit ι n (e^{⊗n}) = ι(e)ⁿ`. -/
theorem powToUnit_app_mPow {L : Y.Modules} (ι : L ⟶ SheafOfModules.unit Y.ringCatSheaf) (W : Y.Opens)
    (e : Γ(L, W)) (n : ℕ) :
    (show Γ(Y, W) from (AlgebraicGeometry.Scheme.Modules.powToUnit ι n).app W
        (AlgebraicGeometry.Scheme.Modules.mPow e n)) =
      (show Γ(Y, W) from ι.app W e) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact AlgebraicGeometry.Scheme.Modules.monoidalUnitIso_hom_app' W (1 : Γ(Y, W))
  | succ n ih =>
    rw [pow_succ, ← ih]
    exact AlgebraicGeometry.Scheme.Modules.powToUnit_app_tensorSections ι n W
      (AlgebraicGeometry.Scheme.Modules.mPow e n) e

/-- Every multiple `r · ι(e)ⁿ` is a value of `powToUnit ι n` on sections over `W` (namely on `r • e^{⊗n}`). -/
theorem exists_powToUnit_app_eq {L : Y.Modules} (ι : L ⟶ SheafOfModules.unit Y.ringCatSheaf) (W : Y.Opens)
    (e : Γ(L, W)) (n : ℕ) (r : Γ(Y, W)) :
    ∃ t : Γ(AlgebraicGeometry.Scheme.Modules.monoidalPow L n, W),
      (show Γ(Y, W) from (AlgebraicGeometry.Scheme.Modules.powToUnit ι n).app W t) =
        r * (show Γ(Y, W) from ι.app W e) ^ n := by
  refine ⟨r • AlgebraicGeometry.Scheme.Modules.mPow e n, ?_⟩
  rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul,
    ← AlgebraicGeometry.Scheme.Modules.powToUnit_app_mPow ι W e n]
  rfl

/-- `powToUnit ι 1` on the pure tensor `1 ⊗ e ∈ Γ(𝟙_ ⊗ L, W)` is `ι(e)`. -/
theorem powToUnit_one_app_tensorSections_one {L : Y.Modules} (ι : L ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (W : Y.Opens) (e : Γ(L, W)) :
    (show Γ(Y, W) from (AlgebraicGeometry.Scheme.Modules.powToUnit ι 1).app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ Y.Modules) L W (1 : Γ(Y, W)) e)) =
      ι.app W e := by
  have h := AlgebraicGeometry.Scheme.Modules.powToUnit_app_tensorSections ι 0 W (1 : Γ(Y, W)) e
  have h0 : (show Γ(Y, W) from (AlgebraicGeometry.Scheme.Modules.powToUnit ι 0).app W (1 : Γ(Y, W))) = 1 :=
    AlgebraicGeometry.Scheme.Modules.monoidalUnitIso_hom_app' W (1 : Γ(Y, W))
  rw [h0, one_mul] at h
  exact h

/-- The inverse left unitor on sections: `(λ_ L).inv (x) = 1 ⊗ x`. -/
theorem leftUnitor_inv_app_eq_tensorSections_one (L : Y.Modules) (W : Y.Opens) (x : Γ(L, W)) :
    (λ_ L).inv.app W x =
      AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ Y.Modules) L W (1 : Γ(Y, W)) x := by
  have h := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections L W (1 : Γ(Y, W)) x
  rw [one_smul] at h
  conv_lhs => rw [← h]
  rw [← ConcreteCategory.comp_apply, ← AlgebraicGeometry.Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
    AlgebraicGeometry.Scheme.Modules.Hom.id_app]
  rfl

end AlgebraicGeometry.Scheme.Modules

end
