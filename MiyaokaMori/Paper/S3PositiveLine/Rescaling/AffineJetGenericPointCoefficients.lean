import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.FrameJetCoefficientMap
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableByCoeff
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetThickeningSectionsCoeff

/-! # The based jet of `ĵ` at the generic point and its coefficients
(helper for Lemma 3.1 of the paper)

The `κ(η_{C̃})`-point `ĵ : T := Spec κ(η) → J_κ^s` over `η_T ≫ ρ : T → C` corresponds, through the
representability of the jet functor (`relativeJetScheme.toBasedJet`), to a based jet
`Θ : D := T ×_k D_κ → 𝒵` over `T` with constant term `s`. This module records:

* `coeff_genericBasedJet`: for an affine open `V ⊆ C` over which `ĵ` lies, the `t^n`-coefficient of
  `Θ^♯ c` (`c ∈ B_V`) is the value of the jet coordinate `d_{n-1} c` at `ĵ`, i.e. `affineJetCoeff n c`
  read in `Γ(T, ⊤) ≅ κ(η) ≅ K(C̃)` (`toBasedJet_appLE_coeff`);
* `coeff_zero_genericBasedJet`: the `t^0`-coefficient is `(ρ^♯ (s^♯ c))(η)` (the constant term of a based
  jet is the seed: `jetConstantTerm_appLE_eq_coeff_zero`, `fromSpecStalk_app`).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **The ring map of `Spec κ(x) → X` on an open `W ∋ x`** is the germ at `x` followed by the residue map
(`fromSpecResidueField = Spec.map (residue x) ≫ fromSpecStalk x`, `fromSpecStalk_app`, `ΓSpecIso_naturality`). -/
theorem AlgebraicGeometry.Scheme.fromSpecResidueField_appLE_apply (X : AlgebraicGeometry.Scheme.{u}) (x : X)
    (W : X.Opens) (hx : x ∈ W)
    (e : (⊤ : (AlgebraicGeometry.Spec (X.residueField x)).Opens) ≤ X.fromSpecResidueField x ⁻¹ᵁ W)
    (a : Γ(X, W)) :
    ((X.fromSpecResidueField x).appLE W ⊤ e).hom a =
      (AlgebraicGeometry.Scheme.ΓSpecIso (X.residueField x)).inv.hom ((X.residue x).hom (X.presheaf.germ W x hx a)) := by
  have e₁ : (⊤ : (AlgebraicGeometry.Spec (X.presheaf.stalk x)).Opens) ≤ X.fromSpecStalk x ⁻¹ᵁ W :=
    fun y _ => by
      show (X.fromSpecStalk x).base y ∈ W
      have hy : (X.fromSpecStalk x).base y ∈ Set.range (X.fromSpecStalk x).base := ⟨y, rfl⟩
      rw [AlgebraicGeometry.Scheme.range_fromSpecStalk] at hy
      exact hy.mem_open W.isOpen hx
  have e₂ : (⊤ : (AlgebraicGeometry.Spec (X.residueField x)).Opens) ≤ AlgebraicGeometry.Spec.map (X.residue x) ⁻¹ᵁ ⊤ :=
    fun _ _ => trivial
  have h1 : (X.fromSpecResidueField x).appLE W ⊤ e =
      (X.fromSpecStalk x).appLE W ⊤ e₁ ≫ (AlgebraicGeometry.Spec.map (X.residue x)).appLE ⊤ ⊤ e₂ := by
    rw [AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE]
    rfl
  have h2 : (X.fromSpecStalk x).appLE W ⊤ e₁ =
      X.presheaf.germ W x hx ≫ (AlgebraicGeometry.Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
    rw [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.fromSpecStalk_app hx, Category.assoc,
      Category.assoc, ← Functor.map_comp]
    have : ((homOfLE (le_top : X.fromSpecStalk x ⁻¹ᵁ W ≤ ⊤)).op ≫ (homOfLE e₁).op :
        Opposite.op (⊤ : (AlgebraicGeometry.Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.comp_id]
  have h3 : (AlgebraicGeometry.Spec.map (X.residue x)).appLE ⊤ ⊤ e₂ =
      (AlgebraicGeometry.Scheme.ΓSpecIso (X.presheaf.stalk x)).hom ≫ X.residue x ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (X.residueField x)).inv := by
    have h := AlgebraicGeometry.Scheme.ΓSpecIso_naturality (X.residue x)
    rw [← Iso.eq_comp_inv, Category.assoc, AlgebraicGeometry.Scheme.Hom.appTop,
      AlgebraicGeometry.Scheme.Hom.app_eq_appLE] at h
    exact h
  rw [h1, h2, h3]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CategoryTheory.Iso.inv_hom_id_apply]

namespace jetNeighborhood

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)

/-- `T := Spec κ(η_{C̃})` as a scheme over `C`, via `η_T ≫ ρ`. -/
def genericOver : CategoryTheory.Over C.toScheme :=
  CategoryTheory.Over.mk (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)

/-- The `k`-structure of `T` used by the based-jet functor (`T → C → Spec k`). -/
@[reducible] def genericOverInst : (genericOver ρ).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨(genericOver ρ).hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩

variable (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
    (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
  (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
    ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)

/-- `ĵ` as a `C`-morphism `T → J_κ^s`. -/
def genericJetHom : genericOver ρ ⟶ relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ :=
  CategoryTheory.Over.homMk ĵ hĵ

/-- **The based jet `Θ` of `ĵ`**: `toBasedJet` of the `C`-morphism `ĵ`. -/
def genericBasedJet :
    (relativeJetFunctor (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).obj
      (Opposite.op (genericOver ρ)) :=
  relativeJetScheme.toBasedJet (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ (genericOver ρ)
    (genericJetHom f κ ρ ĵ hĵ)

include hĵ in
/-- `T.hom ⁻¹ V = ⊤` when `ĵ` lies over `V`. -/
theorem top_le_genericOver_preimage {V : C.toScheme.Opens}
    (hĵV : (⊤ : (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V)) :
    (⊤ : (genericOver ρ).left.Opens) ≤ (genericOver ρ).hom ⁻¹ᵁ V := by
  show (⊤ : (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
    (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom) ⁻¹ᵁ V
  rw [← hĵ, AlgebraicGeometry.Scheme.Hom.comp_preimage]
  exact hĵV

/-- `Θ` maps `pr⁻¹⊤` into `π⁻¹V` when `ĵ` lies over `V`. -/
theorem genericBasedJet_le {V : C.toScheme.Opens} (hVa : AlgebraicGeometry.IsAffineOpen V)
    (hĵV : (⊤ : (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V)) :
    letI := genericOverInst ρ
    jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤ ≤
      (genericBasedJet f κ ρ ĵ hĵ).1 ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) := by
  letI := genericOverInst ρ
  intro x hx
  have h1 : x ∈ jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ((genericOver ρ).hom ⁻¹ᵁ V) :=
    top_le_genericOver_preimage f κ ρ ĵ hĵ hĵV (show _ ∈ (⊤ : (genericOver ρ).left.Opens) from trivial)
  exact relativeJetScheme.ofBasedJetSections_le (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
    (genericOver ρ) (genericBasedJet f κ ρ ĵ hĵ) ⟨V, hVa⟩ h1

include hĵ in
/-- `pr⁻¹⊤ ≤ pr⁻¹(T.hom⁻¹V)` when `ĵ` lies over `V`. -/
theorem proj_preimage_top_le {V : C.toScheme.Opens}
    (hĵV : (⊤ : (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V)) :
    letI := genericOverInst ρ
    jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤ ≤
      jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ((genericOver ρ).hom ⁻¹ᵁ V) :=
  fun _ _ => top_le_genericOver_preimage f κ ρ ĵ hĵ hĵV trivial

set_option backward.isDefEq.respectTransparency false in
/-- **The coefficients of `Θ^♯ c`**: the `t^n`-coefficient of `Θ^♯ c` on `pr⁻¹⊤` is `affineJetCoeff n c`,
read in `Γ(T, ⊤)` through `K(C̃) ≅ κ(η) ≅ Γ(Spec κ(η), ⊤)` (`toBasedJet_appLE_coeff`, restriction to `⊤`,
`hom_preimage_chartOpen`). -/
theorem coeff_genericBasedJet {V : C.toScheme.Opens} (hVa : AlgebraicGeometry.IsAffineOpen V)
    (hĵV : (⊤ : (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V))
    (n : ℕ) (hn : n ≤ κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)) :
    letI := genericOverInst ρ
    jetThickening.coeff (k := k) κ (genericOver ρ).left ⊤ n hn
        (((genericBasedJet f κ ρ ĵ hĵ).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V)
          (jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤) (genericBasedJet_le f κ ρ ĵ hĵ hVa hĵV)).hom c) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).inv.hom
        (haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
         ρ.source.toScheme.functionFieldIsoResidueField.hom.hom (affineJetCoeff f κ ρ ĵ hVa hĵV n c)) := by
  letI := genericOverInst ρ
  letI := relativeJetScheme.sectionsAlgebra (MMSetup.cone f) V
  haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  have hV' := top_le_genericOver_preimage f κ ρ ĵ hĵ hĵV
  have hO := proj_preimage_top_le f κ ρ ĵ hĵ hĵV
  -- (1) the section on `pr⁻¹⊤` is the restriction of the section on `pr⁻¹(T.hom⁻¹V)`
  have h1 : ((genericBasedJet f κ ρ ĵ hĵ).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V)
        (jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤) (genericBasedJet_le f κ ρ ĵ hĵ hVa hĵV)).hom c =
      ((jetThickening (k := k) κ (genericOver ρ).left).presheaf.map (homOfLE hO).op).hom
        (((genericBasedJet f κ ρ ĵ hĵ).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V)
          (jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ((genericOver ρ).hom ⁻¹ᵁ V))
          (relativeJetScheme.ofBasedJetSections_le (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
            (genericOver ρ) (genericBasedJet f κ ρ ĵ hĵ) ⟨V, hVa⟩)).hom c) :=
    (congrArg (fun φ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
        Γ(jetThickening (k := k) κ (genericOver ρ).left, jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤) => φ.hom c)
      (AlgebraicGeometry.Scheme.Hom.appLE_map (genericBasedJet f κ ρ ĵ hĵ).1 _ (homOfLE hO).op)).symm
  rw [h1]
  -- (2) coefficients commute with restriction
  rw [jetThickening.coeff_restrict (k := k) κ (genericOver ρ).left hV' n hn]
  -- (3) the coefficient on `pr⁻¹(T.hom⁻¹V)` is `ĵ^♯ (chartSections V (d_{n-1} c))`
  have h3 := relativeJetScheme.toBasedJet_appLE_coeff (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
    (genericOver ρ) (genericJetHom f κ ρ ĵ hĵ) ⟨V, hVa⟩ n hn c
  rw [show (genericBasedJet f κ ρ ĵ hĵ) = relativeJetScheme.toBasedJet (k := k) (MMSetup.cone f) (MMSetup.seed f).1
    (MMSetup.seed f).2 κ (genericOver ρ) (genericJetHom f κ ρ ĵ hĵ) from rfl, h3]
  -- (4) restrict `ĵ^♯` from `T.hom⁻¹V` to `⊤`, and move the chart identification into `jetCoordinateSection`
  have h4 : ((genericOver ρ).left.presheaf.map (homOfLE hV').op).hom
      (((genericJetHom f κ ρ ĵ hĵ).left.appLE
        (relativeJetScheme.chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hVa⟩)
        ((genericOver ρ).hom ⁻¹ᵁ V)
        (relativeJetScheme.over_preimage_le (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
          (genericOver ρ) (genericJetHom f κ ρ ĵ hĵ) ⟨V, hVa⟩)).hom
        ((relativeJetScheme.chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hVa⟩).hom
          (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1
            (MMSetup.seed f).2 V) κ n c))) =
      ((ĵ.appLE ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V) ⊤
        hĵV).hom (jetCoordinateSection f κ ⟨V, hVa⟩
          (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1
            (MMSetup.seed f).2 V) κ n c))) := by
    have e₁ : (⊤ : (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
        ĵ ⁻¹ᵁ relativeJetScheme.chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hVa⟩ := by
      rw [← relativeJetScheme.hom_preimage_chartOpen]; exact hĵV
    have ha := congrArg (fun φ : Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
        relativeJetScheme.chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hVa⟩) ⟶
        Γ(AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)), ⊤) => φ.hom
          ((relativeJetScheme.chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hVa⟩).hom
            (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1
              (MMSetup.seed f).2 V) κ n c)))
      (AlgebraicGeometry.Scheme.Hom.appLE_map ĵ
        (relativeJetScheme.over_preimage_le (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ
          (genericOver ρ) (genericJetHom f κ ρ ĵ hĵ) ⟨V, hVa⟩) (homOfLE hV').op)
    have hb := congrArg (fun φ : Γ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left,
        relativeJetScheme.chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hVa⟩) ⟶
        Γ(AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)), ⊤) => φ.hom
          ((relativeJetScheme.chartSections (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hVa⟩).hom
            (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation (MMSetup.cone f) (MMSetup.seed f).1
              (MMSetup.seed f).2 V) κ n c)))
      (AlgebraicGeometry.Scheme.Hom.map_appLE' ĵ e₁
        (relativeJetScheme.hom_preimage_chartOpen (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ ⟨V, hVa⟩))
    exact ha.trans hb.symm
  rw [h4]
  -- (5) unfold `affineJetCoeff`; the two isomorphisms cancel
  show _ = (AlgebraicGeometry.Scheme.ΓSpecIso _).inv.hom (ρ.source.toScheme.functionFieldIsoResidueField.hom.hom
    (ρ.source.toScheme.functionFieldIsoResidueField.inv.hom ((AlgebraicGeometry.Scheme.ΓSpecIso _).hom.hom _)))
  rw [CategoryTheory.Iso.inv_hom_id_apply, CategoryTheory.Iso.hom_inv_id_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **The constant term of `Θ^♯ c`** is `(ρ^♯ (s^♯ c))(η)` read in `Γ(T, ⊤)`: the based jet `Θ` has constant
term `T.hom ≫ s = η_T ≫ ρ ≫ s` (`jetConstantTerm_appLE_eq_coeff_zero`, `fromSpecResidueField_appLE_apply`). -/
theorem coeff_zero_genericBasedJet {V : C.toScheme.Opens} (hVa : AlgebraicGeometry.IsAffineOpen V)
    (hĵV : (⊤ : (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V))
    {W : ρ.source.toScheme.Opens} (hηW : genericPoint ρ.source.toScheme ∈ W) (hWV : W ≤ ρ.hom ⁻¹ᵁ V)
    (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)) :
    letI := genericOverInst ρ
    jetThickening.coeff (k := k) κ (genericOver ρ).left ⊤ 0 (Nat.zero_le κ)
        (((genericBasedJet f κ ρ ĵ hĵ).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V)
          (jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤) (genericBasedJet_le f κ ρ ĵ hĵ hVa hĵV)).hom c) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).inv.hom
        ((ρ.source.toScheme.residue (genericPoint ρ.source.toScheme)).hom
          (ρ.source.toScheme.presheaf.germ W (genericPoint ρ.source.toScheme) hηW
            ((ρ.hom.appLE V W hWV).hom
              (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
                (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c)))) := by
  letI := genericOverInst ρ
  rw [← jetConstantTerm_appLE_eq_coeff_zero (k := k) κ (genericOver ρ).left ⊤]
  -- the constant term of `Θ` is `T.hom ≫ s`
  have h1 := congrArg (fun φ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      Γ((genericOver ρ).left, ⊤) => φ.hom c)
    (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (jetConstantTerm (k := k) κ (genericOver ρ).left)
      (genericBasedJet f κ ρ ĵ hĵ).1 ((MMSetup.cone f).hom ⁻¹ᵁ V) (jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤) ⊤
      (genericBasedJet_le f κ ρ ĵ hĵ hVa hĵV) (jetConstantTerm_le (k := k) κ (genericOver ρ).left ⊤))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  have h2 : jetConstantTerm (k := k) κ (genericOver ρ).left ≫ (genericBasedJet f κ ρ ĵ hĵ).1 =
      (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom) ≫ (MMSetup.seed f).1 :=
    (genericBasedJet f κ ρ ĵ hĵ).2.2
  have e₀ : (⊤ : (genericOver ρ).left.Opens) ≤
      ((ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom) ≫ (MMSetup.seed f).1) ⁻¹ᵁ
        ((MMSetup.cone f).hom ⁻¹ᵁ V) := by
    rw [← h2]
    exact (jetConstantTerm_le (k := k) κ (genericOver ρ).left ⊤).trans
      (fun x hx => genericBasedJet_le f κ ρ ĵ hĵ hVa hĵV hx)
  rw [appLE_eq_of_eq h2 ((MMSetup.cone f).hom ⁻¹ᵁ V) ⊤ _ e₀]
  -- split `(η_T ≫ ρ) ≫ s` into three ring maps
  have e₁ : (⊤ : (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ⁻¹ᵁ W := by
    intro x _
    show (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)).base x ∈ W
    rw [AlgebraicGeometry.Scheme.fromSpecResidueField_apply]
    exact hηW
  have h3 := congrArg (fun φ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      Γ((genericOver ρ).left, ⊤) => φ.hom c)
    (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE
      (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom) (MMSetup.seed f).1
      ((MMSetup.cone f).hom ⁻¹ᵁ V) V ⊤
      (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)
      (fun x hx => hWV (e₁ hx)))
  have h4 := congrArg (fun φ : Γ(C.toScheme, V) ⟶ Γ((genericOver ρ).left, ⊤) => φ.hom
      (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
        (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c))
    (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE
      (ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme)) ρ.hom V W ⊤ hWV e₁)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  rw [← h3, ← h4]
  exact AlgebraicGeometry.Scheme.fromSpecResidueField_appLE_apply ρ.source.toScheme
    (genericPoint ρ.source.toScheme) W hηW e₁ _

end jetNeighborhood

end
