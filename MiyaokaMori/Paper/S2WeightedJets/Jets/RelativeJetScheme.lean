import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetFunctor
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineConeAffineHom
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.AffineAlgebra

/-! # The relative based jet scheme

The relative jet scheme `J_k^s = J_k^s(Z/C)`: the `C`-scheme representing the relative based jet functor
(§2 of the paper).

`relativeJetScheme` is the `abbrev` `(jetAffineAlgebra Z s hs r).relativeSpec`: `jetAffineAlgebra : C.AffineAlgebra`
packages the chart ring functor `chartFunctor`, the coefficient map `coefficientMap` and the quasi-coherence
`coefficientMap_coequifibered` into an `AffineAlgebra`, and `J_r^s(Z/C)` is its relative Spec;
`jetGradedAffineAlgebra` (`JetAlgebraSheaf`) is the same algebra together with its grading.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Construction: for every affine open `U` of `C`, let `R_U := Γ(C, U)`, `B_U := Γ(Z, π⁻¹U)` (an `R_U`-algebra via
   `π^♯`) and `ε_U := s^♯ : B_U → R_U` the augmentation; the chart ring is `BasedJetAlgebra ε_U r`. It is functorial in
   `U`, with a coefficient map `O_C(U) →` chart ring; when `Z` is affine over `C` the chart rings commute with
   localization of the base (`coequifibered`), so Mathlib's `Scheme.AffineZariskiSite.relativeGluingData` glues the
   `Spec(chart ring)` into a scheme `J_r^s(Z/C)` over `C`. -/

/-- The `Γ(C, U)`-algebra structure on `B_U = Γ(Z, π⁻¹U)`. -/

@[reducible] noncomputable def relativeJetScheme.sectionsAlgebra {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) (U : C.Opens) : Algebra Γ(C, U) Γ(Z.left, Z.hom ⁻¹ᵁ U) :=
  (Z.hom.app U).hom.toAlgebra

/-- Transport of `appLE` along an equality of morphisms. -/

theorem AlgebraicGeometry.Scheme.Hom.appLE_congr_hom {X Y : AlgebraicGeometry.Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

/-- `s⁻¹π⁻¹U = U` (immediate from `s ≫ π = 𝟙`). -/

theorem relativeJetScheme.section_preimage_le {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (U : C.Opens) :
    U ≤ s ⁻¹ᵁ (Z.hom ⁻¹ᵁ U) := by
  rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, hs]; rfl

/-- The augmentation is a left inverse of the structure map: `π^♯_U ≫ s^♯ = 𝟙` (`comp_appLE` and `s ≫ π = 𝟙`). -/

theorem relativeJetScheme.augmentation_comp {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (U : C.Opens) :
    Z.hom.app U ≫ s.appLE (Z.hom ⁻¹ᵁ U) U (relativeJetScheme.section_preimage_le Z s hs U) =
      CategoryTheory.CategoryStruct.id Γ(C, U) := by
  have h1 : (s ≫ Z.hom).appLE U U (relativeJetScheme.section_preimage_le Z s hs U) =
      Z.hom.app U ≫ s.appLE (Z.hom ⁻¹ᵁ U) U (relativeJetScheme.section_preimage_le Z s hs U) :=
    AlgebraicGeometry.Scheme.Hom.comp_appLE s Z.hom U U _
  have h2 : (s ≫ Z.hom).appLE U U (relativeJetScheme.section_preimage_le Z s hs U) =
      (CategoryTheory.CategoryStruct.id C).appLE U U le_rfl :=
    AlgebraicGeometry.Scheme.Hom.appLE_congr_hom hs U U _ le_rfl
  have h3 : (CategoryTheory.CategoryStruct.id C).appLE U U le_rfl =
      CategoryTheory.CategoryStruct.id Γ(C, U) := by
    simp only [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.Hom.id_app]
    exact C.presheaf.map_id _
  exact h1.symm.trans (h2.trans h3)

/-- The `commutes'` field of the augmentation: `ε_U(π^♯ a) = a`. -/

theorem relativeJetScheme.augmentation_commutes {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (U : C.Opens) (a : Γ(C, U)) :
    (s.appLE (Z.hom ⁻¹ᵁ U) U (relativeJetScheme.section_preimage_le Z s hs U)).hom
        ((Z.hom.app U).hom a) = a := by
  have h := congrArg (fun φ : Γ(C, U) ⟶ Γ(C, U) => CommRingCat.Hom.hom φ a)
    (relativeJetScheme.augmentation_comp Z s hs U)
  simp at h
  exact h

/-- The augmentation `ε_U = s^♯ : Γ(Z, π⁻¹U) → Γ(C, U)` (using `s⁻¹π⁻¹U = U`). -/

noncomputable def relativeJetScheme.augmentation {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C)
    (U : C.Opens) :
    letI := relativeJetScheme.sectionsAlgebra Z U
    Γ(Z.left, Z.hom ⁻¹ᵁ U) →ₐ[Γ(C, U)] Γ(C, U) :=
  letI := relativeJetScheme.sectionsAlgebra Z U
  { toRingHom := (s.appLE (Z.hom ⁻¹ᵁ U) U (relativeJetScheme.section_preimage_le Z s hs U)).hom
    commutes' := relativeJetScheme.augmentation_commutes Z s hs U }

/-- The chart ring `J_r(B_U, ε_U)` over `U`. -/

noncomputable def relativeJetScheme.chartRing {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C)
    (r : ℕ) (U : C.Opens) : CommRingCat.{u} :=
  letI := relativeJetScheme.sectionsAlgebra Z U
  CommRingCat.of (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U) r)

/-- `BasedJetAlgebra.map` is the identity when `ρ` and `β` are identity maps. -/

private theorem bja_map_id_of {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (r : ℕ) (ρ : R →+* R) (β : B →+* B)
    (hβ : ∀ (a : R) (b : B), β (a • b) = ρ a • β b) (hε : ∀ b : B, ε (β b) = ρ (ε b))
    (hρ' : ∀ a, ρ a = a) (hβ' : ∀ b, β b = b) :
    BasedJetAlgebra.map ε ε r ρ β hβ hε = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    show Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) = _
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, hρ']
    rfl
  · intro i
    show Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i)) = _
    rw [MvPolynomial.eval₂Hom_X', hβ']
    rfl

/-- The composition law for `BasedJetAlgebra.map`. -/

private theorem bja_map_comp_of {R B R' B' R'' B'' : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing R'] [CommRing B'] [Algebra R' B'] [CommRing R''] [CommRing B''] [Algebra R'' B'']
    (ε : B →ₐ[R] R) (ε' : B' →ₐ[R'] R') (ε'' : B'' →ₐ[R''] R'') (r : ℕ)
    (ρ : R →+* R') (β : B →+* B') (hβ₁ hε₁)
    (ρ' : R' →+* R'') (β' : B' →+* B'') (hβ₂ hε₂)
    (ρ'' : R →+* R'') (β'' : B →+* B'') (hβ₃ hε₃)
    (hρc : ∀ a, ρ'' a = ρ' (ρ a)) (hβc : ∀ b, β'' b = β' (β b)) :
    BasedJetAlgebra.map ε ε'' r ρ'' β'' hβ₃ hε₃ =
      (BasedJetAlgebra.map ε' ε'' r ρ' β' hβ₂ hε₂).comp
        (BasedJetAlgebra.map ε ε' r ρ β hβ₁ hε₁) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    show Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
      BasedJetAlgebra.map ε' ε'' r ρ' β' hβ₂ hε₂
        (Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)))
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, RingHom.comp_apply,
      hρc]
    show _ = Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C (ρ a)))
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  · intro i
    show Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i)) =
      BasedJetAlgebra.map ε' ε'' r ρ' β' hβ₂ hε₂
        (Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i)))
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', hβc]
    show _ = Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X (i.1, β i.2)))
    rw [MvPolynomial.eval₂Hom_X']

/-- Naturality of `π^♯`: `res_C ≫ π^♯_V = π^♯_U ≫ res_Z`. -/

theorem relativeJetScheme.structure_naturality {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) {U V : C.Opens} (hle : V ≤ U) :
    C.presheaf.map (CategoryTheory.homOfLE hle).op ≫ Z.hom.app V =
      Z.hom.app U ≫ Z.left.presheaf.map (CategoryTheory.homOfLE
        (show Z.hom ⁻¹ᵁ V ≤ Z.hom ⁻¹ᵁ U from
          (TopologicalSpace.Opens.map Z.hom.base).monotone hle)).op :=
  AlgebraicGeometry.Scheme.Hom.naturality Z.hom (CategoryTheory.homOfLE hle).op

/-- Restriction is compatible with the scalar action (a proof obligation for the `map` of `chartFunctor`). -/

theorem relativeJetScheme.chartFunctor_smul {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) {U V : C.Opens} (hle : V ≤ U) :
    letI := relativeJetScheme.sectionsAlgebra Z U
    letI := relativeJetScheme.sectionsAlgebra Z V
    ∀ (a : Γ(C, U)) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U)),
      (Z.left.presheaf.map (CategoryTheory.homOfLE
          (show Z.hom ⁻¹ᵁ V ≤ Z.hom ⁻¹ᵁ U from
            (TopologicalSpace.Opens.map Z.hom.base).monotone hle)).op).hom (a • b) =
        (C.presheaf.map (CategoryTheory.homOfLE hle).op).hom a •
          (Z.left.presheaf.map (CategoryTheory.homOfLE
            (show Z.hom ⁻¹ᵁ V ≤ Z.hom ⁻¹ᵁ U from
              (TopologicalSpace.Opens.map Z.hom.base).monotone hle)).op).hom b := by
  intro a b
  show (Z.left.presheaf.map _).hom ((Z.hom.app U).hom a * b) =
    (Z.hom.app V).hom ((C.presheaf.map _).hom a) * (Z.left.presheaf.map _).hom b
  rw [map_mul]
  refine congrArg (· * _) ?_
  have h := congrArg (fun φ : Γ(C, U) ⟶ Γ(Z.left, Z.hom ⁻¹ᵁ V) => CommRingCat.Hom.hom φ a)
    (relativeJetScheme.structure_naturality Z hle)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.symm

/-- Restriction is compatible with the augmentation (a proof obligation for the `map` of `chartFunctor`). -/

theorem relativeJetScheme.augmentation_naturality {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) {U V : C.Opens} (hle : V ≤ U) :
    Z.left.presheaf.map (CategoryTheory.homOfLE
          (show Z.hom ⁻¹ᵁ V ≤ Z.hom ⁻¹ᵁ U from
            (TopologicalSpace.Opens.map Z.hom.base).monotone hle)).op ≫
        s.appLE (Z.hom ⁻¹ᵁ V) V (relativeJetScheme.section_preimage_le Z s hs V) =
      s.appLE (Z.hom ⁻¹ᵁ U) U (relativeJetScheme.section_preimage_le Z s hs U) ≫
        C.presheaf.map (CategoryTheory.homOfLE hle).op := by
  rw [AlgebraicGeometry.Scheme.Hom.map_appLE, AlgebraicGeometry.Scheme.Hom.appLE_map]

/-- Functoriality of the chart rings in the affine open: restriction maps are induced via `BasedJetAlgebra.map`. -/

noncomputable def relativeJetScheme.chartFunctor {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C)
    (r : ℕ) : C.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := relativeJetScheme.chartRing Z s hs r U.unop.1
  map {U V} f :=
    letI := relativeJetScheme.sectionsAlgebra Z U.unop.1
    letI := relativeJetScheme.sectionsAlgebra Z V.unop.1
    CommRingCat.ofHom (BasedJetAlgebra.map (relativeJetScheme.augmentation Z s hs U.unop.1)
      (relativeJetScheme.augmentation Z s hs V.unop.1) r
      (C.presheaf.map (CategoryTheory.homOfLE
        (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.unop.le)).op).hom
      (Z.left.presheaf.map (CategoryTheory.homOfLE
        (show Z.hom ⁻¹ᵁ V.unop.1 ≤ Z.hom ⁻¹ᵁ U.unop.1 from
          (TopologicalSpace.Opens.map Z.hom.base).monotone
            (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.unop.le))).op).hom
      (relativeJetScheme.chartFunctor_smul Z
        (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.unop.le))
      (fun b => congrArg (fun φ : Γ(Z.left, Z.hom ⁻¹ᵁ U.unop.1) ⟶ Γ(C, V.unop.1) =>
        CommRingCat.Hom.hom φ b) (relativeJetScheme.augmentation_naturality Z s hs
          (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.unop.le))))
  map_id U := by
    letI := relativeJetScheme.sectionsAlgebra Z U.unop.1
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_ofHom]
    refine bja_map_id_of _ _ _ _ _ _ ?_ ?_
    · intro a
      exact congrArg (fun φ : Γ(C, U.unop.1) ⟶ Γ(C, U.unop.1) => CommRingCat.Hom.hom φ a)
        (C.presheaf.map_id (Opposite.op U.unop.1))
    · intro b
      exact congrArg
        (fun φ : Γ(Z.left, Z.hom ⁻¹ᵁ U.unop.1) ⟶ Γ(Z.left, Z.hom ⁻¹ᵁ U.unop.1) =>
          CommRingCat.Hom.hom φ b)
        (Z.left.presheaf.map_id (Opposite.op (Z.hom ⁻¹ᵁ U.unop.1)))
  map_comp {U V W} f g := by
    have hUV : V.unop.1 ≤ U.unop.1 :=
      AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.unop.le
    have hVW : W.unop.1 ≤ V.unop.1 :=
      AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono g.unop.le
    letI := relativeJetScheme.sectionsAlgebra Z U.unop.1
    letI := relativeJetScheme.sectionsAlgebra Z V.unop.1
    letI := relativeJetScheme.sectionsAlgebra Z W.unop.1
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_ofHom]
    refine bja_map_comp_of _ _ _ _ _ _
      (relativeJetScheme.chartFunctor_smul Z hUV)
      (fun b => congrArg (fun φ : Γ(Z.left, Z.hom ⁻¹ᵁ U.unop.1) ⟶ Γ(C, V.unop.1) =>
        CommRingCat.Hom.hom φ b) (relativeJetScheme.augmentation_naturality Z s hs hUV))
      _ _
      (relativeJetScheme.chartFunctor_smul Z hVW)
      (fun b => congrArg (fun φ : Γ(Z.left, Z.hom ⁻¹ᵁ V.unop.1) ⟶ Γ(C, W.unop.1) =>
        CommRingCat.Hom.hom φ b) (relativeJetScheme.augmentation_naturality Z s hs hVW))
      _ _ _ _ ?_ ?_
    · intro a
      exact congrArg (fun φ : Γ(C, U.unop.1) ⟶ Γ(C, W.unop.1) => CommRingCat.Hom.hom φ a)
        (C.presheaf.map_comp (CategoryTheory.homOfLE hUV).op (CategoryTheory.homOfLE hVW).op)
    · intro b
      exact congrArg
        (fun φ : Γ(Z.left, Z.hom ⁻¹ᵁ U.unop.1) ⟶ Γ(Z.left, Z.hom ⁻¹ᵁ W.unop.1) =>
          CommRingCat.Hom.hom φ b)
        (Z.left.presheaf.map_comp
          (CategoryTheory.homOfLE ((TopologicalSpace.Opens.map Z.hom.base).monotone hUV)).op
          (CategoryTheory.homOfLE ((TopologicalSpace.Opens.map Z.hom.base).monotone hVW)).op)

/-- `BasedJetAlgebra.map` is compatible with the coefficients (`algebraMap`). -/

private theorem bja_map_algebraMap {R B R' B' : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing R'] [CommRing B'] [Algebra R' B'] (ε : B →ₐ[R] R) (ε' : B' →ₐ[R'] R') (r : ℕ)
    (ρ : R →+* R') (β : B →+* B')
    (hβ : ∀ (a : R) (b : B), β (a • b) = ρ a • β b) (hε : ∀ b : B, ε' (β b) = ρ (ε b)) :
    (BasedJetAlgebra.map ε ε' r ρ β hβ hε).comp
        (algebraMap R (BasedJetAlgebra ε r)) =
      (algebraMap R' (BasedJetAlgebra ε' r)).comp ρ := by
  refine RingHom.ext fun a => ?_
  show Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) = _
  rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  rfl

/-- The coefficient map `O_C(U) → J_r(B_U, ε_U)`. -/

noncomputable def relativeJetScheme.coefficientMap {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C)
    (r : ℕ) :
    (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor C).op ⋙ C.presheaf ⟶
      relativeJetScheme.chartFunctor Z s hs r where
  app U :=
    letI := relativeJetScheme.sectionsAlgebra Z U.unop.1
    CommRingCat.ofHom (algebraMap Γ(C, U.unop.1)
      (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.unop.1) r))
  naturality {U V} f := by
    letI := relativeJetScheme.sectionsAlgebra Z U.unop.1
    letI := relativeJetScheme.sectionsAlgebra Z V.unop.1
    apply CommRingCat.hom_ext
    exact (bja_map_algebraMap _ _ r _ _
      (relativeJetScheme.chartFunctor_smul Z
        (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.unop.le))
      (fun b => congrArg (fun φ : Γ(Z.left, Z.hom ⁻¹ᵁ U.unop.1) ⟶ Γ(C, V.unop.1) =>
        CommRingCat.Hom.hom φ b) (relativeJetScheme.augmentation_naturality Z s hs
          (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.unop.le)))).symm

/-- When `Z` is affine over `C`, the jet algebra commutes with localization of the base:
`J_r(B_U, ε_U)_f = J_r(B_{D(f)}, ε_{D(f)})` (`B_{D(f)} = (B_U)_f`, and Hasse–Schmidt type algebras commute with
localization; the affine version of Ein–Mustață Lemma 2.3).

Proof:
1. `coequifibered_iff_forall_isLocalizationAway` reduces this to: for every affine open `U` and `f ∈ Γ(C, U)`,
   `J_r(B_{D(f)}, ε_{D(f)})` is the localization of `J_r(B_U, ε_U)` away from the coefficient `f`.
2. `Γ(C, D(f)) = Γ(C,U)[1/f]` (`IsAffineOpen.isLocalization_basicOpen`); `Z → C` affine implies `π⁻¹U` affine,
   `π⁻¹D(f) = D(π^♯ f)` and `Γ(Z, π⁻¹D(f)) = (B_U)[1/π^♯ f]` (`isLocalization_of_eq_basicOpen`).
3. The ring-level lemma `BasedJetAlgebra.isLocalization_away_map`: the based jet algebra commutes with
   localization of the base. -/

theorem relativeJetScheme.coefficientMap_coequifibered {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    (relativeJetScheme.coefficientMap Z s hs r).Coequifibered := by
  rw [AlgebraicGeometry.Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  letI := relativeJetScheme.sectionsAlgebra Z (U.basicOpen f).1
  have hle : (U.basicOpen f).1 ≤ U.1 :=
    AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono (U.basicOpen_le f)
  have hUZ : AlgebraicGeometry.IsAffineOpen (Z.hom ⁻¹ᵁ U.1) := U.2.preimage Z.hom
  exact BasedJetAlgebra.isLocalization_away_map
    (relativeJetScheme.augmentation Z s hs U.1)
    (relativeJetScheme.augmentation Z s hs (U.basicOpen f).1) r
    (C.presheaf.map (CategoryTheory.homOfLE hle).op).hom
    (Z.left.presheaf.map (CategoryTheory.homOfLE
      (show Z.hom ⁻¹ᵁ (U.basicOpen f).1 ≤ Z.hom ⁻¹ᵁ U.1 from
        (TopologicalSpace.Opens.map Z.hom.base).monotone hle)).op).hom
    (relativeJetScheme.chartFunctor_smul Z hle)
    (fun b => congrArg (fun φ : Γ(Z.left, Z.hom ⁻¹ᵁ U.1) ⟶ Γ(C, (U.basicOpen f).1) =>
      CommRingCat.Hom.hom φ b) (relativeJetScheme.augmentation_naturality Z s hs hle))
    f (U.2.isLocalization_basicOpen f)
    (hUZ.isLocalization_of_eq_basicOpen ((Z.hom.app U.1).hom f) _
      (AlgebraicGeometry.Scheme.preimage_basicOpen Z.hom f))

/-- **The jet coordinate algebra as an `AffineAlgebra` on `C`** — the one construction the based
relative jet scheme is built from: affine open `U ↦ J_r(B_U, ε_U)` (`chartFunctor`), structure map the
coefficient map, quasi-coherence `coefficientMap_coequifibered`. `jetGradedAffineAlgebra`
(`JetAlgebraSheaf`) is this algebra together with its grading. -/
noncomputable def jetAffineAlgebra {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    C.AffineAlgebra where
  ring := relativeJetScheme.chartFunctor Z s hs r
  unit := relativeJetScheme.coefficientMap Z s hs r
  coequifibered := relativeJetScheme.coefficientMap_coequifibered Z s hs r

/-- The gluing data `(jetAffineAlgebra Z s hs r).gluingData` (the `Spec J_r(B_U, ε_U)` over `U`;
`AffineZariskiSite.relativeGluingData` of the quasi-coherence proof). Kept as an `abbrev` for the
modules that name it. -/
abbrev relativeJetScheme.gluingData {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    (AlgebraicGeometry.Scheme.AffineZariskiSite.directedCover C).RelativeGluingData :=
  (jetAffineAlgebra Z s hs r).gluingData

/-- **J_r^s(Z/C)** = Spec_C of the jet coordinate algebra (`AffineAlgebra.relativeSpec`). The
parameters `k`, `[C.Over (Spec k)]` are unused and kept only so that the modules passing them keep
compiling. -/
abbrev relativeJetScheme {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    CategoryTheory.Over C :=
  (jetAffineAlgebra Z s hs r).relativeSpec

/-- The chart `Spec J_r(B_U, ε_U) → J` is an open immersion. -/

instance relativeJetScheme.chart_isOpenImmersion {C : AlgebraicGeometry.Scheme.{u}}
    (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (U : C.AffineZariskiSite) :
    AlgebraicGeometry.IsOpenImmersion ((relativeJetScheme.gluingData Z s hs r).cover.f U) :=
  AlgebraicGeometry.Scheme.Cover.map_prop (relativeJetScheme.gluingData Z s hs r).cover U

end
